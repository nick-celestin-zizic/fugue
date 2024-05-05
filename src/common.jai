#if OS == .WASM
then current_time_seconds :: () -> float64 #foreign;
else current_time_seconds :: () -> float64 { return to_float64_seconds(current_time_monotonic()); };

#program_export "load"
load :: (src: string) -> string {
    using context.fugue_state;
    context.print_style.struct_printer = my_struct_printer;
    reset(*memory);
    memory.block_allocator = context.default_allocator;
    PushState(context.allocator, .{pool_allocator_proc, *context.fugue_state.memory});
    
    // we capture log_errors to display in the debugger window
    error := String_Builder.{allocator=temp};
    PushState(context.logger_data, *error);
    PushState(context.logger, (message: string, data: *void, info: Log_Info) {
        if !message then return;
        if (info.common_flags & .ERROR) == 0
        then write_strings(message, "\n");
        else {
            sb := cast(*String_Builder) data;
            append(sb, message);
            append(sb, "<br>");
        }
    });
    using Short_Circuit_Macros(#code { return builder_to_string(*error,, temp); }).{};
    
    source_code = join("", src);
    
    ok: bool;
    vm, prog, typer, ok = load_program(source_code);
    Try(ok);
    
    main_body, ok = table_find(*prog.words, "main");
    Try(ok);
    
    Try(interpret_words(*vm, *prog.words, main_body));
    final_output = builder_to_string(*output);
    
    return "";
}

load_program :: (src: string) -> Virtual_Machine, Program, Typer, bool {
    // log("LOADING PROGRAM");
    ast, ok := parse(src);
    if !ok return .{}, .{}, .{}, false;
    // log("PARSED");
    types:, ok = typecheck_program(*ast);
    if !ok return .{}, .{}, .{}, false;
    // log("TYPED");
    vm: Virtual_Machine;
    remember_allocators(*vm.bindings);
    if !interpret_words(*vm, *ast.words, ast.loose) return .{}, .{}, .{}, false;
    // log("RAN METAPROGRAM");
    // log("LOADED PROGRAM");
    return vm, ast, types, true;
}

#import "Pool";
#import "Basic";
#import "String";
#import "Hash_Table";
#add_context fugue_state: struct {
    using prog   : Program;
    using typer  : Typer;
    using vm     : Virtual_Machine;
    main_body    : []FWord; // TODO: vm should contain tape that contains the whole program with main at the start of the []FWord
    final_output : string;
    ip           : int;
    source_code  : string;
    memory       : Pool;
}

// parser
Macro :: struct {
    args: []string;
    body: []FWord;
}



FDict :: Table(string, []FWord);
TDict :: Table(string, []TWord);
Program :: struct {
    words: FDict;
    types: TDict;
    globl: TDict;
    loose: []FWord;
}


// TODO: These should be the structures we use and Typer should not persist past load()

// Procedure :: struct {
//     body: []FWord;    // View into flattenned program tape
//     args: []*FType;
//     type: [][]*FType; // Trace of type stack
// }

// Program :: struct {
//     words: Table(string, Procedure);
//     types: Table(string, []TWord);
//     loose: Procedure;
//     tapes: []TWord;
// }

// Virtual_Machine :: struct {
//     ip: int;
//     regs_top := 0; // index to top register
//     vars_top := 0; // index to top of variable buffer
//     regs: [32]int;
//     vars: [512]u8;
//     output: String_Builder;
//     call_stack: [..]string;
// }




// typer
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

FType :: struct {
    using data: Tagged(union {
        stk: Type_Stack; // user defined stack of types
        num: void;       // s64
        adr: void;       // *void
        bul: void;       // boolean
        ptr: *FType;     // pops type and pushes pointer to type
        buf: struct { ptr: *FType; count: int; } // fixed sized array
        // unresolved type
        name: string;
    });
    const: Const;
    
    Const :: struct {
        type: Type_Stack;
        data: []u8;
    };
}

TWord :: Tagged(union {
    push_type  : *FType;
    pointerify : void;
    add_name   : string;
    name       : string;
});

Locals :: struct {
    current_offset : u32 = 0;
    bindings: Table(string, Type_Stack_Item);
}

Type_Stack :: []Type_Stack_Item;
Type_Stack_Item :: struct {
    type   : *FType;
    name   : string; // "" for name is equal to using in jai
    offset : u32;
}

// interpreter
Virtual_Machine :: struct {
    regs_top := 0; // index to top register
    vars_top := 0; // index to top of variable buffer
    regs: [32]int;
    vars: [512]u8;
    output: String_Builder;
    
    // TODO: get_var should just refer to the var buffer instead of this sillyness
    bindings: Table(string, int); // name -> index to start in var_buf
    
    
    // tape: []FWord; // TODO: compile to final list of words and patch jumps
}

Put_Var :: struct { name: string; type: []TWord; };
Push_Str :: struct { s: string; #place s; count: int; data: *u8; };

FWord :: Tagged(union {
    push_int: int;
    push_str: Push_Str;
    
    hole: void;
    
    add: void;
    sub: void;
    div: void;
    gt: void;
    lt: void;
    get: *FType;
    put: void;
    
    // stack manipulation
    // (a b)     -> rot(1) -> (b a)
    // (a b c)   -> rot(2) -> (c a b)
    // (a b c d) -> rot(3) -> (d a b c)
    rot  : int;
    dup  : int;
    drop : int;
    over : int;
    
    // after parsing `type` is a word list, after typechecking
    // `type` is a single PUSH_TYPE tword, this is dumb but hopefully temporary
    get_var: string;
    // put_var: Tagged(union{unresolved: Tuple(string, []TWord); resolved: Type_Stack_Item;});
    put_var: Put_Var;
    
    macro : struct { name: string; call: Macro; };
    call  : string;
    
    castt: []TWord;
    
    putc: void;
    putb: void;
    puti: void;
    puts: void;
    puta: void;
    
    // ret: void;
    jmp: u32; // index to next index in FWord tape
    jif: u32; // index to next index in FWord tape
    
    size_of_type: []TWord; // this gets desugared to a PUSH_INT during typechecking
    // temporary temporary unresolved name
    // so that we can have order independent declarations
    name: string;
});

// taggged union
Tagged :: struct (U: Type) {
    #insert -> string {
        sb: String_Builder;
        append(*sb, "T :: enum {\n");
        for type_info(U).members print(*sb, "    %;\n", to_upper_copy_new(it.name));
        append(*sb, "};");
        return builder_to_string(*sb);
    };
    type : T;
    as   : U;
}

Tuple :: struct (types: ..Type) {
    #insert -> string {
        sb: String_Builder;
        for types print(*sb, "_%: %;\n", it_index, it);
        return builder_to_string(*sb);
    }
}

PushState :: (var: Code, val: Code) #expand {
    old := (#insert var);
    (#insert var) = (#insert val);
    `defer (#insert var) = old;
}

Short_Circuit_Macros :: struct (on_fail: Code) #type_info_none {
    Try :: (cond: bool, fmt := "", args: ..Any, cleanup := #code,null, scope := #caller_code, loc := #caller_location) #expand {
        if !cond Throw(fmt, ..args, cleanup=cleanup, scope=scope, loc=loc);
    }
    Throw :: (fmt := "", args: ..Any, cleanup := #code,null, scope := #caller_code, loc := #caller_location) #expand {
        #if fmt {
            log_error(fmt, ..args, loc=loc);
            // log_stack_trace(context.stack_trace);
        }
        #if cleanup #insert,scope(scope) cleanup;
        #insert,scope(scope) on_fail;
    }
}

my_struct_printer :: (sb: *String_Builder, v: Any, data: *void) -> bool {
    // here we "dereference" any pointer types so that we can print the
    // contents at that address if it is non-null (you can still cast to *void to
    // print the address)
    if !v.value_pointer return false;
    item: Any;
    info: *Type_Info_Struct;
    if v.type.type == {
    case .POINTER; {
        item.value_pointer = (cast(**void)v.value_pointer).*;
        if !item.value_pointer return false;
        item.type = (cast(*Type_Info_Pointer)v.type).pointer_to;
        if item.type.type != .STRUCT return false;
        info = cast(*Type_Info_Struct) item.type;
    }
    case .STRUCT; {
        if !v.value_pointer return false;
        info = cast(*Type_Info_Struct) v.type;
        item = v;
    }
    case; assert(false, "%", v.type.type); return false;
    }
    
    if info.name == {
    case "FType"; {
        type := cast(*FType) item.value_pointer;
        render_type(sb, type.*);
        return true;
    }
    case "Tagged";
        // extract the tag value
        tag_type: *Type_Info_Enum;
        for info.members if it.name == "type" tag_type = xx it.type;
        if !tag_type || tag_type.type != .ENUM return false;
        
        val_type: *Type_Info_Struct;
        for info.members if it.name == "as" val_type = xx it.type;
        if !val_type || val_type.type != .STRUCT return false;
        
        any: Any = ---;
        any.value_pointer = item.value_pointer;
        any.type          = tag_type;
        
        num := (cast(*int)item.value_pointer).*;
        if (num < 0) || (num >= val_type.members.count) {
            print(sb, "(corrupt tagged union with tag %)", num);
            return true;
        }
        
        print_item_to_builder(sb, any);
        if   val_type.members[num].type == type_info(void)
        then return true;
        
        any.value_pointer = item.value_pointer + size_of(int);
        any.type          = val_type.members[num].type;
        print(sb, "(%)", any);
        return true;
    case "Format_Fugue_Value"; {
        format := cast(*Format_Fugue_Value) item.value_pointer;
        render_value(sb, format.item, format.data, format.name);
        return true;
    }
    case "Put_Var"; {
        using cast(*Put_Var) item.value_pointer;
        append(sb, name);
        append(sb, ", ");
        if type.count == 1 && type[0].type == .PUSH_TYPE
        then print_item_to_builder(sb, type[0].as.push_type);
        else print_item_to_builder(sb, type);
        return true;
    }
    case "Push_Str"; {
        // remove the surrouding quotes
        // around the string literals
        str := (cast(*string)item.value_pointer).*;
        str.data  += 1;
        str.count -= 2;
        append(sb, str);
        return true;
    }
    case; if v.type.type != .POINTER then return false; else {
        print_item_to_builder(sb, item);
        return true;
    }
    }
}


render_value :: (sb: *String_Builder, desc: Type_Stack_Item, memory: *void, show_name := true) {
    v := memory + desc.offset;
    if #complete desc.type.type == {
    case .ADR; #through;
    case .PTR; print(sb, "%", (cast(*int)v).*);
    case .BUL; append(sb, ifx (cast(*int)v).* == 0 then "false" else "true");
    case .NUM; print(sb, "%", (cast(*int)v).*);
    case .STK; for desc.type.as.stk {
        render_value(sb, .{
            it.type, ifx show_name && desc.name
            then tprint("%.%", desc.name, it.name) else it.name,
            desc.offset + it.offset
        }, memory);
        if it_index != desc.type.as.stk.count-1 append(sb, " ");
    }
    case .BUF; assert(false, "TODO");
    case .NAME; assert(false);
    case; assert(false, "%", desc.type.type);
    }
    if show_name && desc.name && desc.type.type != .STK
    then print(sb, " name(%)", desc.name);
}

render_type :: (sb: *String_Builder, type: FType) {
    if #complete type.type == {
    case .STK; {
        for type.as.stk {
            render_type(sb, it.type.*);
            if it_index != type.as.stk.count-1 append(sb, " ");
        }
    }
    case .PTR; {
        render_type(sb, type.as.ptr.*);
        append(sb, " ptr");
    }
    case .ADR; append(sb, "addr");
    case .BUL; append(sb, "bool");
    case .NUM; append(sb, "int"); // TODO: different ints
    case .BUF; assert(false, "TODO");
    case .NAME; assert(false, "TODO");
    case; assert(false, "Corrupt tag %", type.type);
    }
}

Format_Fugue_Value :: struct {
    item: Type_Stack_Item;
    data: *void; // base that item.offset is relative to
    name: bool;  // wether to print top-level name() suffix
}