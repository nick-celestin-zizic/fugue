// Since Jai currently only supports compiling to WASM64 (i.e. it requires the "Memory64" extension), you need to enable that feature flag in your browser.
// See https://webassembly.org/roadmap/ for where "Memory64" is available and how you can enable it.

// Thanks to Alexey Kutepov (Tsoding/rexim), Patrik Smělý (SogoCZE), and KujuKuju for laying the groundwork
// for this by figuring out how to use Jai for WASM.

#run {
    set_build_options_dc(.{do_output = false});

    w := compiler_create_workspace("Wasm");
    
    plugins: [..] *Metaprogram_Plugin;
    init_plugins(.["Check(CHECK_BINDINGS=false)"], *plugins, w);

    options := get_build_options(w);
    copy_commonly_propagated_fields(get_build_options(), *options);
    
    options.dead_code_elimination = .MODULES_ONLY;
    options.output_type                         = .EXECUTABLE;
    options.backend                             = .LLVM; // WASM only works with the LLVM backend, obviously.
    options.os_target                           = .WASM;
    options.cpu_target                          = .CUSTOM;
    options.emit_debug_info                     = .DWARF;
    options.backtrace_on_crash                  = .OFF; // Runtime_Support_Crash_Handler doesn’t support WASM (yet?)
    options.output_path                         = "../ICSI499/fugue/src/assets";
    options.output_executable_name              = "main";
    options.llvm_options.target_system_features = "+bulk-memory"; // "This options is needed so that "memcpy" and "memset" are mapped to "memory.copy" and "memory.fill" instructions in WASM.
    options.llvm_options.enable_split_modules   = false;
    options.llvm_options.function_sections      = true; // To get around "LLVM ERROR: section already has a defining function: .text"

    import_paths: [..]string;
    // Add our own modules folder first so that we can override modules with our own version, if necessary.
    array_add(*import_paths, tprint("%modules", #filepath));
    for options.import_path array_add(*import_paths, it);
    options.import_path = import_paths;

    // This was compiled from https://github.com/wingo/walloc via "clang -Oz --target=wasm64 -nostdlib -c -o walloc.o walloc.c".
    // We should probably port this allocator to Jai instead…
    //  -rluba, 2023-11-15
    walloc_object_file_path := "modules/walloc.o";

    STACK_SIZE :: 4096 * 4096;
    options.additional_linker_arguments = .["--stack-first", "-z", tprint("stack-size=%", STACK_SIZE), walloc_object_file_path];
    
    struct_printer_options: My_Struct_Printer;
    context.print_style.struct_printer = my_struct_printer;
    context.print_style.struct_printer_data = *struct_printer_options;
    {   using context.print_style.default_format_struct;
        use_long_form_if_more_than_this_many_members = -1;
        use_newlines_if_long_form = true;
        draw_type_name = true;
        // long_form_separator_between_fields = ";\n";
        // G :: struct {
        //     x    := "cool";
        // }
        // S :: struct {
        //     x    := "cool";
        //     dude := 37;
        //     not  := false;
        //     gee  : *G;
        // }
        // g := New(G);
        // s := New(S);
        // s.gee = g;
        // log("%", s);
        // exit(69);
    }
    
    set_build_options(options, w);
    
    intercept_flags: Intercept_Flags;
    for plugins if it.before_intercept it.before_intercept(it, *intercept_flags);

    // Replace the default allocator with Walloc (https://github.com/wingo/walloc).
    remap_import(w, "*", "Default_Allocator", "Walloc");
    compiler_begin_intercept(w, intercept_flags);
    add_build_file("src/wasm_main.jai", w);
    
    for plugins if it.add_source it.add_source(it);
    
    
    while true {
        message := compiler_wait_for_message();
        for plugins if it.message it.message(it, message);
        if message.kind == {
        case .TYPECHECKED; {
            typechecked := cast(*Message_Typechecked) message;
            // for typechecked.declarations {}
            for body: typechecked.procedure_bodies {
                for expr: body.subexpressions {
                    // insert_tagged_union_access_checks(expr);
                }
            }
        }
        case .COMPLETE; break;
        }
    }

    compiler_end_intercept(w);
    for plugins if it.finish   it.finish  (it);
    for plugins if it.shutdown it.shutdown(it);
}

insert_tagged_union_access_checks :: (expr: *Code_Node) {
    if expr.kind != .BINARY_OPERATOR return;
    
    binop := cast(*Code_Binary_Operator) expr;
    // if binop.operator_type != #char "." return;
    // if binop.left.type.type != .STRUCT  return;
    if binop.right.type.type == .VOID              return; // this happens inside struct literals like .{type=.FOO, as.foo=whatever}
    if binop.left.type.type  != .STRUCT            return;
    if binop.left.kind       != .IDENT             return;
    if (cast(*Code_Ident) binop.left).name != "as" return;
    
    as_type := cast(*Type_Info_Struct) binop.left.type;
    
    // tis := cast(*Type_Info_Struct) binop.left.type;
    // if tis.name != "Tagged" return;
    
    
    using expr.location;
    log("%:%:%: %", enclosing_load.fully_pathed_filename, l0, c0, to_string(expr));
    // log("left  type %", as_type);
    // log("right type %", binop.right);
}

#import "Program_Print";
to_string :: (code: *Code_Node) -> string /*temp*/ {
    b := String_Builder.{allocator=temp};
    print_expression(*b, code);
    return builder_to_string(*b,, temp);
}

PushState :: (var: Code, val: Code) #expand {
    old := (#insert var);
    (#insert var) = (#insert val);
    `defer (#insert var) = old;
}

My_Struct_Printer :: struct {
    current_pointer_depth := 0;
    max_pointer_depth := 3;
}
my_struct_printer :: (sb: *String_Builder, v: Any, data: *void) -> bool {
    // here we "dereference" any pointer types so that we can print the
    // contents at that address if it is non-null (you can still cast to *void to
    // print the address)
    assert(xx data);
    using cast(*My_Struct_Printer) data;
    
    if !v.value_pointer return false;
    item: Any;
    if v.type.type == .POINTER {
        if current_pointer_depth > max_pointer_depth
        then return false;
        else {
            item.value_pointer = (cast(**void)v.value_pointer).*;
            if !item.value_pointer return false;
            item.type = (cast(*Type_Info_Pointer)v.type).pointer_to;
            current_pointer_depth += 1;
            if context.print_style.default_format_struct.draw_type_name
            then append(sb, "*");
            print_item_to_builder(sb, item);
            current_pointer_depth -= 1;
            return true;
        }
    }
    
    return false;
    
    // v.type.type != .POINTER
    
    // if info.name == {
    // case "Tagged";
    //     // extract the tag value
    //     tag_type: *Type_Info_Enum;
    //     for info.members if it.name == "type" tag_type = xx it.type;
    //     if !tag_type || tag_type.type != .ENUM return false;
        
    //     val_type: *Type_Info_Struct;
    //     for info.members if it.name == "as" val_type = xx it.type;
    //     if !val_type || val_type.type != .STRUCT return false;
        
    //     any: Any = ---;
    //     any.value_pointer = item.value_pointer;
    //     any.type          = tag_type;
        
    //     num := (cast(*int)item.value_pointer).*;
    //     if (num < 0) || (num >= val_type.members.count) {
    //         print_to_builder(sb, "(corrupt tagged union with tag %)", num);
    //         return true;
    //     }
        
    //     print_item_to_builder(sb, any);
    //     if   val_type.members[num].type == type_info(void)
    //     then return true;
        
    //     any.value_pointer = item.value_pointer + size_of(int);
    //     any.type          = val_type.members[num].type;
    //     print_to_builder(sb, "(%)", any);
    //     return true;
    // case; if v.type.type != .POINTER then return false; else {
    //     print_item_to_builder(sb, item);
    //     return true;
    // }
    // }
}

#import "Metaprogram_Plugins";
#import "Basic";
#import "Compiler";
#import "Print_Vars";
// #import "File";
// #import "String";
// #import "System";
