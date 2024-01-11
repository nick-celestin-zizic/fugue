// TODO: floats
TYPE_INT :: FType.{type=.NUM}; // TODO: signed/unsigned and smaller sized integers
TYPE_ADR :: FType.{type=.ADR};

make_type_pointer :: (using t: *Typer, c: FType.Const, ptr_to: *FType) -> *FType {
    // TODO: pointer type caches in typer
    assert(ptr_to != null);
    t := New(FType, false);
    t.type   = .PTR;
    t.as.ptr = ptr_to;
    t.const  = c;
    return t;
}

make_type_buffer :: (using t: *Typer, c: FType.Const, ptr_to: *FType, size: u64) -> *FType {
    // TODO: buffer type caches in typer
    assert(false);
    return null;
}

make_type_stack :: (using t: *Typer, c: FType.Const, items: []Type_Stack_Item) -> *FType {
    t := New(FType, false);
    t.type   = .STK;
    t.as.stk = items;
    t.const  = c;
    return t;
}

make_type_name :: (using t: *Typer, c: FType.Const, name: string) -> *Type {
    assert(false);
    return null;
}


operator == :: (a: FType, b: FType) -> bool {
    if a.type != b.type return false;
    #insert -> string {
        ti_union := type_info(type_of(a.as));
        ti_enum  := type_info(type_of(a.type));
        sb: String_Builder;
        append(*sb, "if a.type == {\n");
        for ti_union.members {
            upper := to_upper_copy_new(it.name,, temp);
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
    type   : *FType;
    name   : string; // "" for name is equal to using in jai
    offset : u32;
}

Type_Builder :: struct {
    current_offset : u32 = 0;
    types          : [..]Type_Stack_Item;
    const_types    : [..]Type_Stack_Item;
    const_data     : [..]u8;
}

build_type :: (using tb: *Type_Builder, typer: *Typer, word: TWord) -> bool {
    if #complete word.type == {
    case .PUSH_TYPE;
        array_add(*types, .{word.as.push_type, "", current_offset});
        current_offset += runtime_size(word.as.push_type);
    case .ADD_NAME;
        if !types return false;
        types[types.count-1].name = word.as.add_name;
    case .POINTERIFY;
        if !types return false;
        t := types[types.count-1].type;
        types[types.count-1].type = make_type_pointer(typer, .{}, t);
    case .NAME; assert(false, "internal compiler error: unresolved type name %", word.as.name);
    }
    return true;
}

builder_to_type :: (typer: *Typer, tb: *Type_Builder) -> *FType {
    // @Leak the array into the type heap oh well nabd gets cleared later
    return ifx tb.types.count == 1 && tb.types[0].name == "" && !tb.const_data
    then tb.types[0].type else make_type_stack(typer, .{tb.const_types, tb.const_data}, tb.types);
}

type_builder_free :: (using tb: Type_Builder) {
    array_free(types);
    array_free(const_types);
    array_free(const_data);
}

runtime_size :: (t: FType) -> u32 {
    if #complete t.type == {
    case .NUM; return 8;
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


Typer :: struct {
    types: *TDict; // this is from the program
    global_scope := Table(string, Type_Stack_Item).{allocator=temp};
    // pointer_type_cache := Table(*FType, *FType).{allocator=temp};
    // buffer_type_cache  := Table(struct{p:*FType;c:int;}, *FType).{allocator=temp};
}

extract_type :: (ts: []TWord) -> *FType {
    if ts.count != 1 {
        // TODO: better logs
        log_error("count %", ts);
        return null;
    }
    if ts[0].type != .PUSH_TYPE {
        // TODO: better logs
        log_error("type %", ts);
        return null;
    }
    if ts[0].as.push_type == null {
        // TODO: better logs
        log_error("null %", ts);
        return null;
    }
    return ts[0].as.push_type;
}

typecheck_program :: (program: *Program) -> bool {
    push_allocator(program.allocator);
    auto_release_temp();
    typer := Typer.{types=*program.types};
    
    using Short_Circuit_Macros(#code { return false; }).{};
    
    // TODO: this is all fucked up
    // the whole point of resolve_type being its own proc
    // is so that we can do a recursive dynamic programming thing
    // where we keep trying to resolve each type as we encounter a new name
    // so that we can have composed types that were defined out of order
    for * program.types {
        t := eval_type(*typer, it.*);
        if t {
            it.count = 1;
            it.*[0]  = .{type=.PUSH_TYPE, as.push_type=t};
        }
    }
    
    // type metaprogram and save global variable types
    locals := Locals.{bindings.allocator=temp};
    type_stack: [..]*FType; type_stack.allocator = temp;
    
    for *program.loose {
        Check(type_word(*typer, *program.words, *locals, *type_stack, it));
    }
    
    Check(type_stack.count == 0, "unhandled items on the global scope stack! %", type_stack);
    
    typer.global_scope = locals.bindings;
    locals = .{bindings.allocator=temp};
    
    body, ok := table_find(*program.words, "main");
    Check(ok, "You did not define main!");
    
    for *body Check(type_word(*typer, *program.words, *locals, *type_stack, it));
    Check(type_stack.count == 0, "unhandled items on the global scope stack! %", type_stack);
    
    return true;
}

Locals :: struct {
    current_offset : u32 = 0;
    bindings: Table(string, Type_Stack_Item);
}

type_word :: (
    using typer : *Typer,
    words       : *FDict,
    locals      : *Locals,
    type_stack  : *[..]*FType,
    word        : *FWord
) -> bool {
    assert(xx typer);
    assert(xx words);
    assert(xx locals);
    assert(xx type_stack);
    assert(xx word);
    
    using Short_Circuit_Macros(#code { assert(false, "%", type_stack.*); return false; }).{};
    Pop :: (caller := #caller_code) -> *FType #expand {
        Check(type_stack.count > 0, "Type stack underflow!", caller=caller);
        a := type_stack.*[type_stack.count-1];
        type_stack.count -= 1;
        return a;
    }
    
    // defer log("% ==> %", word.*, type_stack.*);
    
    if #complete word.type == {
    case .PUSH_INT; array_add(type_stack, *TYPE_INT);
    case .PUSH_STR; array_add(type_stack, *TYPE_INT, *TYPE_ADR);
    case .ADD; #through; case .DIV; {
        a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
        b := Pop(); Check(b.type == .NUM, "expected int but got %", b);
        array_add(type_stack, *TYPE_INT);
    }
    case .SIZE_OF_TYPE; {
        // we technically leak the the []TWord on word.as.size_of_type,
        // but all allocations are pooled per compilation so we don't care
        t := eval_type(typer, word.as.size_of_type);
        Check(t != null);
        word.* = .{type=.PUSH_INT, as.push_int=runtime_size(t)};
        array_add(type_stack, *TYPE_INT);
    }
    case .GET; {
        a := Pop();
        if a.type == {
        case .STK; assert(false, "%", a.as.stk);
        case .PTR; push_type(type_stack, a.as.ptr); word.as.get = a.as.ptr;
        case; Fail("expected ptr type but got %", a.type);
        }
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
        t, ok := table_find(*global_scope, word.as.get_var);
        if ok {
            array_add(type_stack, make_type_pointer(typer, .{}, t.type));
            return true;
        }
        
        assert(false, "internal compiler error: variable % could not be found", word.as.get_var);
    }
    case .PUT_VAR; using word.as.put_var; {
        assert(type.count > 0);
        t: *FType;
        if type.count == 1 && type[0].type == .NAME && type[0].as.name == "" {
            // infer type as top register
            t = Pop();
            type[0] = .{type=.PUSH_TYPE, as.push_type=t};
        } else if type.count == 1 && type[0].type == .PUSH_TYPE {
            // type was already resolved or is simple enough not to need resolution
            t = type[0].as.push_type;
            if !pop_type(type_stack, t) return false;
        } else {
            // evaluate type expression and cache the type
            t = eval_type(typer, type);
            Check(t != null);
            if !pop_type(type_stack, t) return false;
            type.count = 1;
            type[0] = .{type=.PUSH_TYPE, as.push_type=t};
        }
        if locals {
            table_set(*locals.bindings, name, .{t, name, locals.current_offset});
            locals.current_offset = runtime_size(t);
        }
    }
    case .ROT; {
        assert(word.as.rot > 0);
        if word.as.rot != 1 assert(false, "TODO: rot(%)", word.as.rot);
        a := Pop();
        b := Pop();
        push_type(type_stack, a);
        push_type(type_stack, b);
    }
    case .MACRO; using word.as.macro; {
        assert(call.body.count != 0, "internal compiler error: unresolved macro %", name);
        for *call.body if !type_word(typer, words, locals, type_stack, it) return false;
    }
    case .CALL; {
        body, ok := table_find(words, word.as.call);
        Check(ok, "undefined word %", word.as.call);
        // TODO: we need to have seperate locals!!!!
        for *body Check(type_word(typer, words, locals, type_stack, it));
    }
    case .PUTC; a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
    case .PUTI; a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
    case .PUTA; a := Pop(); Check(a.type == .ADR || a.type == .PTR, "expected addr or ptr but got %", a);
    case .PUTS; {
        data  := Pop(); Check(data.type == .ADR, "expected addr but got %", data);
        count := Pop(); Check(count.type == .NUM, "expected int but got %", count);
    }
    case .CASTT; {
        t := Pop();
        t  = eval_type(typer, word.as.castt);
        Check(t != null);
        array_add(type_stack, t);
    }
    case .PROC_BEGIN;
    case .PROC_END;
    case .NAME; assert(false, "internal compiler error: unresolved name %", word.as.name);
    }
    return true;
}

eval_type :: (using typer: *Typer, words: []TWord) -> *FType {
    tb: Type_Builder;
    
    using Short_Circuit_Macros(#code {
        type_builder_free(*tb);
        return null;
    }).{};
    
    for words if it.type == {
        case .NAME; {
            ts, ok := table_find(types, it.as.name);
            Check(ok, "type % is not defined", it.as.name);
            for ts Check(build_type(*tb, typer, it));
        }
        case; Check(build_type(*tb, typer, it));
    }
    
    t := builder_to_type(typer, *tb);
    return t;
}

push_type :: (type_stack: *[..]*FType, type: *FType) -> bool {
    assert(type != null);
    if #complete type.type == {
    case .STK; {
        // TODO: maybe need to sort by offset?
        for < type.as.stk if !push_type(type_stack, it.type) return false;
        return true;
    }
    case .NUM; array_add(type_stack, type); return true;
    case .ADR; array_add(type_stack, type); return true;
    case .PTR; array_add(type_stack, type); return true;
    case .BUF; assert(false, "TODO: %", type);
    case .NAME; assert(false, "internal compiler error: unresolved name %", type.as.name);
    }
    return true;
}

pop_type :: (type_stack: *[]*FType, type: *FType) -> bool {
    Pop :: () -> FType #expand {
        if type_stack.count < 1 {
            log_error("type stack undeflow!!");
            `return false;
        }
        a := type_stack.*[type_stack.count-1];
        type_stack.count -= 1;
        return a;
    }
    
    if type.type == .STK {
        // log("stack %", type.as.stk);
        for type.as.stk  if !pop_type(type_stack, it.type) return false;
        return true;
    } else {
        a := Pop();
        // log("popped %", a);
        if (a != type) && (type.type == .ADR && a.type == .PTR) {
            log_error("%: expected % but got %", #procedure_name(), type, a);
            return false;
        }
    }
    return true;
}