Fugue_State :: struct {
    using prog  : Program;
    using typer : Typer;
    using vm    : Virtual_Machine;
    main_body   : []FWord;
    memory      : Pool;
}

state: Fugue_State;
load :: (src: string) -> bool {
    using state;
    reset(*memory);
    memory.block_allocator = context.allocator;
    PushState(context.allocator, .{pool_allocator_proc, *state.memory});
    context.print_style.struct_printer = my_struct_printer;
    
    vm=, prog=, typer=, ok := load_program(src);
    if !ok return false;
    
    main_body, ok = table_find(*prog.words, "main");
    return ok;
} @JsExport

print_instructions :: (to_dom: bool) {
    PushStateIf(context.logger, dom_logger, to_dom);
    for state.main_body log("[%] %", it_index, it);
}


get_two :: () -> bool, string {
    return false, "hello";
} @JsExport

get_inst :: () -> string {
    sb: String_Builder;
    for state.main_body print_to_builder(*sb, "[%] %\n", it_index, it);
    return builder_to_string(*sb);
} @JsExport

talloc_reg :: () { wasm_set_tallocated(alloc(size_of(int),, temp)); }

run_main :: () -> string {
    using state;
    ok := interpret_words(*vm, *prog.words, main_body);
    PushState(context.logger, dom_logger);
    str := builder_to_string(*vm.output,, temp);
    assert(ok);
    return str;
}

main :: ()  {
    assert(false, "don't call main, this is a library!");
    // procs called here are so that they do not get removed by dead code elimination
    reset_temporary_storage();
    talloc(0);
}

get_type_tag :: (t: Type) -> int {
    if t == {
        case *void;   return 0;
        case  s32;    return 1;
        case  int;    return 2;
        case  string; return 3;
        case  bool;   return 4;
        case; assert(false, "unsupported type %", t); return -1;
    }
}

load_program :: (src: string) -> Virtual_Machine, Program, Typer, bool {
    ast, ok := parse(src);
    if !ok return .{}, .{}, .{}, false;
    types:, ok = typecheck_program(*ast);
    if !ok return .{}, .{}, .{}, false;
    vm: Virtual_Machine;
    remember_allocators(*vm.bindings);
    if !interpret_words(*vm, *ast.words, ast.loose) return .{}, .{}, .{}, false;
    return vm, ast, types, true;
}

dom_logger :: (message: string, data: *void, info: Log_Info) {
    is_error := (info.common_flags & .ERROR) != 0;
    wasm_log_dom(message.count, message.data, is_error);
}

wasm_set_tallocated :: (val: *void)                            #foreign;
wasm_log_dom        :: (count: s64, data: *u8, is_error: bool) #foreign;
wasm_write_string   :: (count: s64, data: *u8, is_error: bool) #foreign;

// TODO: have @JsExport notes that create wrapper procs so we can have sane return types
make_string :: (count: int, data: *void) -> int {
    str := New(string, initialized=false,, temp);
    str.count = count; str.data = data;
    return cast,force(int) (cast(*void) str);
}

// taggged union
Tagged :: struct (U: Type) {
    #insert -> string {
        sb: String_Builder;
        append(*sb, "T :: enum {\n");
        for type_info(U).members print_to_builder(*sb, "    %;\n", to_upper_copy_new(it.name));
        append(*sb, "};");
        return builder_to_string(*sb);
    };
    type : T;
    as   : U;
}

Tuple :: struct (types: ..Type) {
    #insert -> string {
        sb: String_Builder;
        for types print_to_builder(*sb, "_%: %;\n", it_index, it);
        return builder_to_string(*sb);
    }
}

PushState :: (var: Code, val: Code) #expand {
    old := (#insert var);
    (#insert var) = (#insert val);
    `defer (#insert var) = old;
}

PushStateIf :: (var: Code, val: Code, cond: bool) #expand {
    old := (#insert var);
    (#insert var) = ifx cond then (#insert val) else old;
    `defer (#insert var) = old;
}

Short_Circuit_Macros :: struct (on_fail: Code) #type_info_none {
    Check :: (cond: bool, $fmt := "", args: ..Any, cleanup := #code,null, caller := #caller_code) #expand {
        if !cond Fail(fmt, ..args, cleanup=cleanup, caller=caller);
    }
    Fail :: ($fmt := "", args: ..Any, cleanup := #code,null, caller := #caller_code) #expand {
        #if fmt log_error("%: %", #procedure_name(), tprint(fmt, ..args));
        #if cleanup #insert,scope(caller) cleanup;
        #insert,scope(caller) on_fail;
    }
}

my_struct_printer :: (sb: *String_Builder, v: Any, _: *void) -> bool {
    // here we "dereference" any pointer types so that we can print the
    // contents at that address if it is non-null (you can still cast to *void to get addr)
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
        append(sb, "*");
    }
    case .STRUCT; {
        if !v.value_pointer return false;
        info = cast(*Type_Info_Struct) v.type;
        item = v;
    }
    case; assert(false, "%", v.type.type); return false;
    }
    
    if info.name == {
    case "FType";
        // don't show constant storage when debug printing FTypes
        info = cast(*Type_Info_Struct) info.members[0].type;
        #through;
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
            print_to_builder(sb, "(corrupt tagged union with tag %)", num);
            return true;
        }
        
        print_item_to_builder(sb, any);
        if   val_type.members[num].type == type_info(void)
        then return true;
        
        any.value_pointer = item.value_pointer + size_of(int);
        any.type          = val_type.members[num].type;
        print_to_builder(sb, "(%)", any);
        return true;
    case; if v.type.type != .POINTER then return false; else {
        print_item_to_builder(sb, item);
        return true;
    }
    }
}

FDict :: Table(string, []FWord);
TDict :: Table(string, []TWord);
Program :: struct {
    words: FDict;
    types: TDict;
    globl: TDict;
    loose: []FWord;
}

FWord :: Tagged(union {
    push_int: int;
    push_str: string;
    
    add: void;
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
    
    // after parsing `type` is a word list, after typechecking
    // `type` is a single PUSH_TYPE tword, this is dumb but hopefully temporary
    get_var: string;
    // put_var: Tagged(union{unresolved: Tuple(string, []TWord); resolved: Type_Stack_Item;});
    put_var: struct { name: string; type: []TWord; };
    
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

Macro :: struct {
    args: []string;
    body: []FWord;
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


#import "Basic";
#import "String";
#import "Hash_Table";
#import "Pool";
#load "../src/parser.jai";
#load "../src/typer.jai";
#load "../src/interpreter.jai";
