// TODO: floats
TYPE_INT :: FType.{type=.NUM}; // TODO: signed/unsigned and smaller sized integers
TYPE_ADR :: FType.{type=.ADR};
TYPE_BUL :: FType.{type=.BUL};

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


compare_bytes :: (a: *void, b: *void, count: s64) -> s16 {
    for 0..count-1 {
        d := cast(s16) (((cast(*u8)a)+it).* - ((cast(*u8)b)+it).*);
        if d != 0 return d;
    }
    return 0;
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
                "case .%1; return compare_bytes(*a.as.%2, *b.as.%2, %3) == 0;\n",
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
        o := current_offset;
        current_offset += runtime_size(word.as.push_type);
        assert(current_offset > o);
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
    case .BUL; return 8;
    case .BUF; return runtime_size(t.as.buf.ptr.*) * cast(u32) t.as.buf.count;
    case .STK; {
        big_offset : u32 = 0;
        big_size   : u32 = 0;
        for t.as.stk {
            if it.offset >= big_offset {
                size := runtime_size(it.type);
                if it.offset+size > big_offset+big_size {
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
    global_scope : Table(string, Type_Stack_Item);
    local_scope  : Locals;
    type_stack   : [..]*FType;
    stacks       : [..][]*FType;
    backpatches  : Table(u32, u32); // dst -> src (indices into stacks)
    // last_ip      := -1;
    // stacks       : Table(u32, Tuple([]*FType, int));
    // pointer_type_cache := Table(*FType, *FType).{allocator=temp};
    // buffer_type_cache  := Table(struct{p:*FType;c:int;}, *FType).{allocator=temp};
}

push_stack :: (using,only(stacks, type_stack) typer: *Typer) {
    // log("%", stacks);
    if stacks.count >= stacks.allocated {
        reserve := 2 * stacks.allocated;
        if reserve < 8 then reserve = 8;
        array_reserve(*stacks, reserve);
        stacks.count += 1;
        stacks[stacks.count-1] = array_copy(type_stack);
    } else {
        stacks.count += 1;
        if stacks[stacks.count-1].data != null {
            array_resize(*stacks[stacks.count-1], type_stack.count, false);
            // log("    % %", stacks[stacks.count-1].data, type_stack);
            if type_stack memcpy(
                stacks[stacks.count-1].data, type_stack.data,
                type_stack.count*size_of(type_of(type_stack[0]))
            );
        } else {
            stacks[stacks.count-1] = array_copy(type_stack);
        }
        // log("    % %", stacks[stacks.count-1], type_stack);
    }
}

reset_stacks :: (typer: *Typer) {
    array_reset_keeping_memory(*typer.stacks);
    array_reset_keeping_memory(*typer.type_stack);
    table_reset(*typer.backpatches);
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

typecheck_program :: (program: *Program) -> Typer, bool {
    using Short_Circuit_Macros(#code { return .{}, false; }).{};
    
    typer := Typer.{};
    
    // TODO: this is all fucked up
    // the whole point of resolve_type being its own proc
    // is so that we can do a recursive dynamic programming thing
    // where we keep trying to resolve each type as we encounter a new name
    // so that we can have composed types that were defined out of order
    for * program.types {
        t := eval_type(*typer, *program.types, it.*);
        if t {
            it.count = 1;
            it.*[0]  = .{type=.PUSH_TYPE, as.push_type=t};
        }
    }
    
    // type metaprogram and save global variable types
    Check(type_words(*typer, *program.types, *program.words, program.loose));
    typer.global_scope = typer.local_scope.bindings;
    typer.local_scope.bindings = .{};
    reset_stacks(*typer);
    global_offset := typer.local_scope.current_offset;
    if typer.type_stack.count != 0 {
        log_error("unhandled items on the stack! %", typer.type_stack);
        return .{}, false;
    }
    assert(typer.backpatches.count == 0);
    
    body, ok := table_find(*program.words, "main");
    Check(ok, "You did not define main!");
    Check(type_words(*typer, *program.types, *program.words, body));
    if typer.type_stack.count != 0 {
        log_error("unhandled items on the stack! %", typer.type_stack);
        return .{}, false;
    }
    assert(typer.backpatches.count == 0, "%", typer.backpatches.count);
    
    // reset_stacks(*typer);
    // table_reset(*typer.local_scope.bindings);
    // typer.local_scope.current_offset = global_offset;
    return typer, true;
}

Locals :: struct {
    current_offset : u32 = 0;
    bindings: Table(string, Type_Stack_Item);
}

type_words :: (
    typer: *Typer, types: *TDict,
    words: *FDict, tape: []FWord
) -> bool {
    for * tape {
        // log("!!!!!!!! %", it_index);
        if !type_word(typer, types, words, it, xx it_index) return false;
    }
    return true;
}

// this and that are indices into stacks
// where stacks[ip] is the type stack AFTER an
// instruction at tape[ip] has been executed
// this procedure verifies the following:
// the stack AFTER this must match the stack BEFORE that
stacks_match :: (using typer: *Typer, this: u32, that: u32) -> bool {
    assert(xx stacks);
    a := stacks[this];
    b := ifx that then stacks[that-1] else .[];
    using Short_Circuit_Macros(#code {
        assert(false, "[%] % ?= [%] %\n\n%", this, a, that, b, stacks);
        return false;
    }).{};
    Check(a.count == b.count);
    for a Check(it == b[it_index]);
    return true;
}

// TODO: move locals and type stack into typer so that we can call it from the debugger
type_word :: (using typer: *Typer, types: *TDict, words: *FDict, word: *FWord, ip: u32) -> bool {
    using Short_Circuit_Macros(#code { assert(false, "%", type_stack); return false; }).{};
    Pop :: (caller := #caller_code) -> *FType #expand {
        Check(type_stack.count > 0, "Type stack underflow!", caller=caller);
        a := type_stack[type_stack.count-1];
        type_stack.count -= 1;
        return a;
    }
    
    // log("??? % %", ip, word.*);
    // defer log("[%] % => %", ip, word.*, type_stack);
    
    // check if there is a backpatch needed
    // i.e the type stack after tape[patch] is typed should be
    // the same as the type stack before tape[ip] is typed
    patch, needs_check := table_find(*backpatches, ip);
    if needs_check {
        assert(patch < ip);
        // log("% % % %", patch, ip, stacks.count, type_stack);
        Check(stacks_match(typer, patch, ip));
        table_remove(*backpatches, ip);
    }
    
    if #complete word.type == {
    case .LT; #through;
    case .GT; {
        a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
        b := Pop(); Check(b.type == .NUM, "expected int but got %", b);
        array_add(*type_stack, *TYPE_BUL);
    }
    // TODO: we need a way to check that the src and dst for the jumps have the same type stack
    case .JMP; {
        assert(word.as.jmp != ip);
        
        push_stack(typer);
        if word.as.jmp < ip
        then Check(stacks_match(typer, ip, word.as.jmp));
        else table_add(*backpatches, word.as.jmp, ip);
        
        patch, needs_check = table_find(*backpatches, ip+1);
        assert(needs_check);
        array_copy(*type_stack, stacks[patch]);
        table_remove(*backpatches, ip+1);
        return true;
    }
    case .JIF; {
        a := Pop();
        Check(a.type == .BUL, "expected bool but got %", a);
        assert(word.as.jif != ip);
        if word.as.jif < ip {
            // we need to push the stack rn so that we can compare properly
            push_stack(typer);
            Check(stacks_match(typer, ip, word.as.jif));
            return true;
        } else table_add(*backpatches, word.as.jif, ip);
        // if word.as.jif < ip 
        // then Check(stacks_match(typer, word.as.jif));
        // else { table_add(*backpatches, word.as.jif, cast(u32) ip); log("added patch to %", ip); }
    }
    
    case .PUSH_INT; array_add(*type_stack, *TYPE_INT);
    case .PUSH_STR; array_add(*type_stack, *TYPE_INT, *TYPE_ADR);
    case .ADD; #through; case .DIV; {
        a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
        b := Pop(); Check(b.type == .NUM, "expected int but got %", b);
        array_add(*type_stack, *TYPE_INT);
    }
    case .SIZE_OF_TYPE; {
        // we technically leak the the []TWord on word.as.size_of_type,
        // this is dumb.
        t := eval_type(typer, types, word.as.size_of_type);
        Check(t != null);
        word.* = .{type=.PUSH_INT, as.push_int=runtime_size(t)};
        array_add(*type_stack, *TYPE_INT);
    }
    case .GET; {
        a := Pop();
        if a.type == {
        case .STK; assert(false, "%", a.as.stk);
        case .PTR; push_type(*type_stack, a.as.ptr); word.as.get = a.as.ptr;
        case; Fail("expected ptr type but got %", a.type);
        }
    }
    case .PUT; assert(false, "TODO: PUT");
    case .GET_VAR; {
        info, ok := table_find(*local_scope.bindings, word.as.get_var);
        if ok then array_add(*type_stack, make_type_pointer(typer, .{}, info.type));
        else {
            t:, ok = table_find(*global_scope, word.as.get_var);
            assert(ok, "internal compiler error: variable % could not be found", word.as.get_var);
            array_add(*type_stack, make_type_pointer(typer, .{}, t.type));
        }
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
            Check(pop_type(*type_stack, t));
        } else {
            // evaluate type expression and cache the type
            t = eval_type(typer, types, type);
            Check(t != null);
            Check(pop_type(*type_stack, t));
            type.count = 1;
            type[0] = .{type=.PUSH_TYPE, as.push_type=t};
        }
        table_set(*local_scope.bindings, name, .{t, name, local_scope.current_offset});
        local_scope.current_offset += runtime_size(t);
    }
    case .ROT; {
        assert(word.as.rot > 0);
        if word.as.rot != 1 assert(false, "TODO: rot(%)", word.as.rot);
        a := Pop();
        b := Pop();
        push_type(*type_stack, a);
        push_type(*type_stack, b);
    }
    case .DUP; {
        assert(word.as.dup > 0);
        t := Pop();
        for 0..word.as.dup push_type(*type_stack, t);
    }
    case .DROP; {
        assert(word.as.drop > 0);
        for 1..word.as.drop Pop();
    }
    case .MACRO; using word.as.macro; {
        assert(call.body.count != 0, "internal compiler error: unresolved macro %", name);
        // log("MACRO START");
        Check(type_words(typer, types, words, call.body));
        // log("MACRO END");
    }
    case .CALL; {
        body, ok := table_find(words, word.as.call);
        Check(ok, "undefined word %", word.as.call);
        // TODO: we need to have seperate local scope!!!!
        Check(type_words(typer, types, words, body));
    }
    case .PUTC; a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
    case .PUTB; a := Pop(); Check(a.type == .BUL, "expected bool but got %", a);
    case .PUTI; a := Pop(); Check(a.type == .NUM, "expected int but got %", a);
    case .PUTA; a := Pop(); Check(a.type == .ADR || a.type == .PTR, "expected addr or ptr but got %", a);
    case .PUTS; {
        data  := Pop(); Check(data.type == .ADR, "expected addr but got %", data);
        count := Pop(); Check(count.type == .NUM, "expected int but got %", count);
    }
    case .CASTT; {
        t := Pop();
        t  = eval_type(typer, types, word.as.castt);
        Check(t != null);
        array_add(*type_stack, t);
    }
    case .NAME; assert(false, "internal compiler error: unresolved name %", word.as.name);
    case;
    }
    
    push_stack(typer);
    return true;
}

eval_type :: (using typer: *Typer, types: *TDict, words: []TWord) -> *FType {
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
    case .NAME; assert(false, "internal compiler error: unresolved name %", type.as.name);
    case .BUF; assert(false, "TODO: %", type);
    case .BUL; array_add(type_stack, type); return true;
    case .NUM; array_add(type_stack, type); return true;
    case .ADR; array_add(type_stack, type); return true;
    case .PTR; array_add(type_stack, type); return true;
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
    
    // log("    popping % %", runtime_size(type), type);
    
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