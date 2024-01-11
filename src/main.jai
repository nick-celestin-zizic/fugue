FDict :: Table(string, []FWord);
TDict :: Table(string, []TWord);
Program :: struct {
    words: FDict;
    types: TDict;
    globl: TDict;
    loose: []FWord;
    
    allocator := Allocator.{proc=pool_allocator_proc};
    #place allocator; _: void;
    memory_handle: *Pool;
}

FWord :: Tagged(union {
    push_int: int;
    push_str: string;
    
    add: void;
    div: void;
    get: *FType;
    put: void;
    
    // stack manipulation
    // (a b)     -> rot(1) -> (b a)
    // (a b c)   -> rot(2) -> (c a b)
    // (a b c d) -> rot(3) -> (d a b c)
    rot: int;
    
    // after parsing `type` is a word list, after typechecking
    // `type` is a single PUSH_TYPE tword, this is dumb but hopefully temporary
    get_var: string;
    put_var: struct { name: string; type: []TWord; };
    
    macro : struct { name: string; call: Macro; };
    call  : string;
    
    castt: []TWord;
    
    putc: void;
    puti: void;
    puts: void;
    puta: void;
    
    proc_begin  : void;
    proc_end    : void;
    // proc_return : void;
    
    // if_begin : int; // index to corresponsing if_end
    // if_else  : int; // index to corresponsing if_end
    // if_end   : void;
    
    // while_begin : void;
    // while_do    : int; // index to end
    // while_end   : int; // index to begin
    
    // defer_begin : void;
    // defer_end   : void;
    
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
        num: void; // s64
        adr: void; // *void
        ptr: *FType; // pops type and pushes pointer to type
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

main :: () {
    context.print_style.default_format_struct.use_long_form_if_more_than_this_many_members = 3;
    context.print_style.struct_printer = my_struct_printer;
    args := get_command_line_arguments();
    if args.count != 2 {
        log_error("usage: % <input path>", args[0]);
        return;
    }
    
    src, ok := read_entire_file(args[1]);
    if !ok return;
    
    ast:, ok = parse(src);
    if !ok return;
    
    ok = typecheck_program(*ast);
    if !ok return;
    
    ok = interpret_program(*ast);
    if !ok return;
}

using Basic  :: #import "Basic";
using String :: #import "String";
using F      :: #import "File";
using HT     :: #import "Hash_Table";
using P      :: #import "Pool";
using BA     :: #import "Bucket_Array";
#load "parser.jai";
#load "interpreter.jai";
#load "typer.jai";

program_free :: (using program: Program) {
    for words array_free(it);
    // for types array_free(it); // @Leak TODO: type_free() or something fo macros and nested stuff
    deinit(*words);
    deinit(*types);
    array_free(loose);
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
        tag_type := cast(*Type_Info_Enum) info.members[1].type;
        val_type := cast(*Type_Info_Struct) info.members[2].type;
        
        any: Any = ---;
        any.value_pointer = item.value_pointer;
        any.type          = tag_type;
        print_item_to_builder(sb, any);
        
        num := (cast(*int)item.value_pointer).*;
        if val_type.members[num].type == type_info(void)
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

// TODO: stack manipulation primitives
// dup  or dup(num > 0)
// rot  or rot(num > 0)
// over or over(num > 0)
// drop or drop(num > 0)

// TODO: dynamic memory primitives
// pools: pcreate/palloc/prealloc/pclear/pdispose
// heaps: hcreate/halloc/hrealloc/hfree/hclear/hdispose
// TODO: default allocators
// macro talloc   temporary_storage palloc   end
// macro trealloc temporary_storage prealloc end
// macro tclear   temporary_storage pclear   end
// macro malloc   global_heap halloc   end
// macro mrealloc global_heap hrealloc end
// macro mfree    global_heap hfree    end

// TODO: we only need the const mechanism to get enums
/*
type tag int
    name(PUSH_INT) const(0)
    name(PUSH_INT) const(1 +)
    name(PUSH_INT) const(1 +)
    name(PUSH_INT) const(1 +)
    name(PUSH_INT) const(1 +)
    name(PUSH_INT) const(1 +)
end
*/

// TODO: this currently doesn't work but should
/*
type mlist array
    int name(capacity)
end
type tlist array
    int name(capacity)
end
type plist array
    int      name(capacity)
    pool ptr name(pool)
end
*/

// TODO: field getters and setters for typestacks
// var(vec, int name(x) int int name(z) int)
// 69  vec!x
// 420 vec!z

// TODO: allocate a zero initialized var on the data stack
// push_var(buf, u8(256))
// push_var(len, u32)