Type :: struct {
    type  : Tag;
    as    : Data;
    const : Const;
    
    Tag :: enum {
        STK; // user defined stack of types (structs/unions/enums)
        INT; // s64
        ADR; // *void
        PTR; // pops type and pushes pointer to type
        BUF; // fixed sized array
        // TEMPORARY thing that gets resolved when parse completes
        NAME;
    };
    
    Data :: union {
        ptr: *Type;
        buf: struct { ptr: *Type; count: int; }
        stk: Type_Stack;
        name: string;
    };
    
    Const :: struct {
        type: Type_Stack;
        data: []u8;
    };
}

// TODO: floats
TYPE_INT :: Type.{type=.INT}; // TODO: signed/unsigned and smaller sized integers
TYPE_ADR :: Type.{type=.ADR};

make_type_pointer :: (using t: *Typer, c: Type.Const, ptr_to: *Type) -> *Type {
    // TODO: pointer type caches in typer
    assert(ptr_to != null);
    t := New(Type, false, allocator);
    t.type   = .PTR;
    t.as.ptr = ptr_to;
    t.const  = c;
    return t;
}

make_type_buffer :: (using t: *Typer, c: Type.Const, ptr_to: *Type, size: u64) -> *Type {
    // TODO: buffer type caches in typer
    assert(false);
    return null;
}

make_type_stack :: (using t: *Typer, c: Type.Const, items: []Type_Stack_Item) -> *Type {
    t := New(Type, false, allocator);
    t.type   = .STK;
    t.as.stk = items;
    t.const  = c;
    return t;
}

make_type_name :: (using t: *Typer, c: Type.Const, name: string) -> *Type {
    assert(false);
    return null;
}


operator == :: (a: Type, b: Type) -> bool {
    if a.type != b.type return false;
    #insert -> string {
        ti_union := type_info(type_of(a.as));
        ti_enum  := type_info(type_of(a.type));
        sb: String_Builder;
        append(*sb, "if a.type == {\n");
        for ti_union.members {
            upper := to_upper_copy(it.name);
            if array_find(ti_enum.names, upper) then print_to_builder(*sb,
                "case .%1; return memcmp(*a.as.%2, *b.as.%2, %3) == 0;\n",
                upper, it.name, it.type.runtime_size
            );
        }
        append(*sb, "}\n");
        str := builder_to_string(*sb);
        // log(str);
        return str;
    }
    return true;
}

Type_Stack :: []Type_Stack_Item;
Type_Stack_Item :: struct {
    type   : *Type;
    name   : string; // "" for name is equal to using in jai
    offset : u32;
}

Type_Builder :: struct {
    current_offset : u32 = 0;
    types          : [..]Type_Stack_Item;
    const_types    : [..]Type_Stack_Item;
    const_data     : [..]u8;
}

build_type :: (using tb: *Type_Builder, word: Type_Word) -> bool {
    if #complete word.type == {
    case .PUSH_TYPE;
        array_add(*types, .{word.as.push_type, "", current_offset});
        current_offset += runtime_size(word.as.push_type);
    case .ADD_NAME;
        if !types assert(false);
        if types[types.count-1].name != "" assert(false);
        types[types.count-1].name = word.as.add_name;
    case .POINTERIFY;
        assert(false, "%", types);
    case .NAME; assert(false, "internal compiler error: unresolved type name %", word.as.name);
    }
    return true;
}

builder_to_type :: (typer: *Typer, tb: *Type_Builder) -> *Type {
    // @Leak the array into the type heap oh well nabd gets cleared later
    return ifx tb.types.count == 1 && tb.types[0].name == "" && !tb.const_data
    then tb.types[0].type else make_type_stack(typer, .{tb.const_types, tb.const_data}, tb.types);
}

type_builder_free :: (using tb: Type_Builder) {
    array_free(types);
    array_free(const_types);
    array_free(const_data);
}

runtime_size :: (t: Type) -> u32 {
    if #complete t.type == {
        case .INT; return 8;
        case .ADR; return 8;
        case .PTR; return 8;
        case .BUF; return runtime_size(t.as.buf.ptr.*) * cast(u32) t.as.buf.count;
        case .STK; {
            big_offset : u32 = 0;
            big_size   : u32 = 0;
            for t.as.stk {
                if it.offset >= big_offset {
                    size := runtime_size(it.type);
                    if size > big_size {
                        big_offset = it.offset;
                        big_size   = size;
                    }
                }
            }
            return big_offset + big_size;
        }
        case .NAME; assert(false, "internal compiler error: unresolved type name %", t.as.name);
        case; assert(false); return 0;
    }
    assert(false);
    return 0;
}


Type_Table :: Table(string, *Type);
Typer :: struct {
    dictionary   : Type_Table;
    global_types : Table(string, Type_Stack_Item); // global variable types and offset into uninitialized data section
    allocator    : Allocator; #place allocator; _: *void;
    heap         : *Flat_Pool;
    // pointer_types : Table(*Type, *Type);         // uses temporary storage
    // buffer_types  : Table(Type.Data.buf, *Type); // uses temporary storage
}

typer_free :: (using t: *Typer) {
    fini(heap);
    dictionary = .{};
}

typer_reset :: (using t: *Typer) {
    reset(heap);
    dictionary = .{};
}

typer_init :: (using t: *Typer) {
    bootstrap_pool := Flat_Pool.{};
    allocator.proc  = flat_pool_allocator_proc;
    allocator.data  = get(*bootstrap_pool, size_of(Flat_Pool));
    heap.* = bootstrap_pool;
    dictionary.allocator   = allocator;
    global_types.allocator = allocator;
    // pointer_types.allocator = temp;
    // buffer_types.allocator  = temp;
}

typecheck_program :: (using program: *Program) -> Type_Table, Flat_Pool, bool {
    typer: Typer;
    typer_init(*typer);
    
    F :: () #expand {
        typer_free(*typer);
        `return .{}, .{}, false;
    }
    
    // TODO: this is all fucked up
    // the whole point of resolve_type being its own proc
    // is so that we can do a recursive dynamic programming thing
    // where we keep trying to resolve each type as we encounter a new name
    // so that we can type recursive types that were defined out of order
    // for types if !resolve_type(*typer, *types, it_index, it) then F();
    for types table_set(*typer.dictionary, it_index, eval_type(*typer, it));
    
    // for typer.dictionary   log("% ==> %", it_index, it);
    // for globals log("% ==> %", it_index, it);
    
    locals: Locals; locals.bindings.allocator = typer.allocator;
    type_stack: [..]*Type; type_stack.allocator = temp;
    for *loose if !type_word(*typer, *program.words, *locals, *type_stack, it) F();
    if type_stack.count != 0 {
        log_error("unhandled items on the global scope stack! %", type_stack);
        F();
    }
    typer.global_types = locals.bindings;
    locals = .{bindings.allocator=temp};
    
    body, ok := table_find(*program.words, "main");
    if !ok {
        log_error("you didn't define main!!!");
        F();
    }
    
    log("\n\nMAIN\n\n");
    for *body if !type_word(*typer, *program.words, *locals, *type_stack, it) F();
    if type_stack.count != 0 {
        log_error("unhandled items on the main scope stack! %", type_stack);
        F();
    }
    
    return typer.dictionary, typer.heap, true;
}

resolve_type :: (using typer: *Typer, name: string, body: []Type_Word) -> bool {
    _, ok := table_find(*dictionary, name);
    if ok {
        log("name % was already resolved!", name);
        return true;
    }
    
    tb: Type_Builder;
    for body if it.type == .NAME {
        body:, ok = table_find(*dictionary, it.as.name);
        if ok {
            log("type % was defined previously!", it.as.name);
            return true;
        }
        assert(false, "TODO: %", it.as.name);
    } else {
        if !build_type(*tb, it) {
            type_builder_free(*tb);
            return false;
        }
    }
    // TODO: check for redecls
    table_set(*dictionary, name, builder_to_type(typer, *tb));
    return true;
}

Locals :: struct {
    current_offset : u32 = 0;
    bindings: Table(string, Type_Stack_Item);
}

type_word :: (
    using typer : *Typer,
    words       : *Table(string, []Word),
    locals      : *Locals,
    type_stack  : *[..]*Type,
    word        : *Word
) -> bool {
    assert(typer != null);
    assert(words != null);
    // locals can be null for global scope
    assert(type_stack != null);
    assert(word != null);
    
    Fail :: (fmt: string, args: ..Any) #expand { assert(false, fmt, ..args); }
    Pop :: () -> *Type #expand {
        if type_stack.count < 1 {
            log_error("type stack undeflow!");
            `return false;
        }
        a := type_stack.*[type_stack.count-1];
        type_stack.count -= 1;
        return a;
    }
    
    defer log("% ==> %", word, type_stack.*);
    
    if #complete word.type == {
    case .PUSH_INT; array_add(type_stack, *TYPE_INT);
    case .PUSH_STR; array_add(type_stack, *TYPE_INT, *TYPE_ADR);
    case .ADD; {
        a := Pop();
        b := Pop();
        if a.type != .INT Fail("expected int but got %", a.type);
        if b.type != .INT Fail("expected int but got %", b.type);
        array_add(type_stack, *TYPE_INT);
    }
    case .GET; {
        a := Pop();
        if a.type == .STK {
            assert(false, "%", a.as.stk);
        } else if a.type != .PTR Fail("expected ptr type but got %", a.type);
        push_type(type_stack, a.as.ptr);
    }
    case .PUT; assert(false, "TODO: PUT");
    case .GET_VAR; {
        // NOTE: we check locals before globals so that shadowing is possible
        if locals {
            info, ok := table_find(*locals.bindings, word.as.get_var);
            if ok {
                array_add(type_stack, make_type_pointer(typer, .{}, info.type));
                return true;
             }
        }
        t, ok := table_find(*global_types, word.as.get_var);
        if ok {
            array_add(type_stack, make_type_pointer(typer, .{}, t.type));
            return true;
        }
        
        assert(false, "internal compiler error: variable % could not be found", word.as.get_var);
    }
    case .PUT_VAR; using word.as.put_var; {
        assert(type.count > 0);
        t: *Type;
        if type.count == 1 && type[0].type == .NAME && type[0].as.name == "" {
            // infer type as top register
            t = Pop();
            type[0] = .{type=.PUSH_TYPE, as.push_type=t};
        } else if type.count == 1 && type[0].type == .PUSH_TYPE {
            t = type[0].as.push_type;
            if !pop_type(type_stack, t) return false;
        } else {
            t = eval_type(typer, type);
            if !pop_type(type_stack, t) return false;
            type.count = 1;
            type[0] = .{type=.PUSH_TYPE, as.push_type=t};
        }
        if locals {
            table_set(*locals.bindings, name, .{t, name, locals.current_offset});
            locals.current_offset = runtime_size(t);
        }
    }
    case .MACRO; using word.as.macro; {
        assert(call.body.count != 0, "internal compiler error: unresolved macro %", name);
        for *call.body if !type_word(typer, words, locals, type_stack, it) return false;
    }
    case .CALL; {
        body, ok := table_find(words, word.as.call);
        if !ok Fail("undefined word %", word.as.call);
        // TODO: we need to have seperate locals!!!!
        for *body if !type_word(typer, words, locals, type_stack, it) return false;
    }
    case .PUTC; a := Pop(); if a.type != .INT Fail("expected int but got %", a);
    case .PUTI; a := Pop(); if a.type != .INT Fail("expected int but got %", a);
    case .PUTA; a := Pop(); if a.type != .ADR && a.type != .PTR Fail("expected addr or ptr but got %", a);
    case .PUTS; {
        data  := Pop();
        count := Pop();
        if data.type  != .ADR then Fail("expected addr but got %", data.type);
        if count.type != .INT then Fail("expected int but got %", count.type);
    }
    case .PROC_BEGIN;
    case .PROC_END;
    case .NAME; assert(false, "internal compiler error: unresolved name %", word.as.name);
    }
    return true;
}

eval_type :: (using typer: *Typer, words: []Type_Word) -> *Type {
    tb: Type_Builder;
    for words if it.type == .NAME {
        t, ok := table_find(*dictionary, it.as.name);
        if !ok {
            log_error("ERROR: type % is not defined", it.as.name);
            type_builder_free(*tb);
            return null;
        }
        if !build_type(*tb, .{type=.PUSH_TYPE, as.push_type=t}) {
            type_builder_free(*tb);
            return null;
        }
    } else if !build_type(*tb, it) {
        type_builder_free(*tb);
        return null;
    }
    return builder_to_type(typer, *tb);
}

push_type :: (type_stack: *[..]*Type, type: *Type) -> bool {
    assert(type != null);
    if #complete type.type == {
    case .STK; {
        // TODO: maybe need to sort by offset?
        for < type.as.stk if !push_type(type_stack, it.type) return false;
        return true;
    }
    case .INT; array_add(type_stack, type); return true;
    case .ADR; array_add(type_stack, type); return true;
    case .PTR; assert(false, "TODO: %", type);
    case .BUF; assert(false, "TODO: %", type);
    case .NAME; assert(false, "internal compiler error: unresolved name %", type.as.name);
    }
    return true;
}

pop_type :: (type_stack: *[]*Type, type: *Type) -> bool {
    Pop :: () -> Type #expand {
        if type_stack.count < 1 {
            log_error("type stack undeflow!");
            `return false;
        }
        a := type_stack.*[type_stack.count-1];
        type_stack.count -= 1;
        return a;
    }
    
    if type.type == .STK {
        for type.as.stk  if !pop_type(type_stack, it.type) return false;
        return true;
    } else {
        a := Pop();
        if a != type {
            log_error("%: expected % but got %", #procedure_name(), type, a);
            return false;
        }
    }
    return true;
}