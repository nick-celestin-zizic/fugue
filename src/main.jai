Program :: struct {
    words: Table(string, []Word);
    types: Table(string, []Type_Word);
    globl: Table(string, []Type_Word);
    loose: []Word;
}

Word :: struct {
    type: enum {
        PUSH_INT;
        PUSH_STR;
        
        ADD;
        
        GET;
        PUT;
        
        GET_VAR;
        PUT_VAR;
        
        MACRO;
        CALL;
        
        PUTC;
        PUTI;
        PUTS;
        PUTA;
        
        PROC_BEGIN;
        PROC_END;
        
        // IF
        // ELSE_IF
        // ELSE
        // IF_END
        
        // temporary instruction that gets resolved later
        // so that we can order independent declarations
        NAME;
    };
    as: union {
        push_int : int;
        push_str : string;
        call     : string;
        macro    : struct { name: string; call: Macro; };
        get_var  : string;
        put_var  : struct { name: string; type: []Type_Word; }; // after parsing `type` is a word list, after typechecking, `type` is a single PUSH_TYPE instruction, this is dumb but hopefully temporary
        name     : string;
    }
}

Macro :: struct {
    args: []string;
    body: []Word;
}

Type_Word :: struct {
    type: enum {
        PUSH_TYPE;
        POINTERIFY;
        ADD_NAME; // sets the current top Type_Stack_Item's name
        // temporary name that gets resolved before typechecking
        NAME;
    };
    as: union {
        push_type: *Type;
        add_name: string;
        name: string;
    };
}

main :: () {
    context.print_style.struct_printer = (sb: *String_Builder, v: Any, _: *void) -> bool {
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
            if !item.value_pointer return false;
            info = cast(*Type_Info_Struct) v.type;
            item = v;
        }
        case; return false;
        }
        
        if info.name == {
        case "Word";      #through;
        case "Type";      #through;
        case "Type_Word"; #through;
        case "Expr";
            print_tagged_union(sb, item);
            return true;
        case; return false;
        }
    };
    
    args := get_command_line_arguments();
    if args.count != 2 {
        log_error("usage: % <input path>", args[0]);
        return;
    }
    
    src, ok := read_entire_file(args[1]);
    if !ok return;
    
    ast:, ok = parse(src);
    if !ok return;
    
    log("\n====\nTYPECHECKING:");
    types:, _, ok = typecheck_program(*ast);
    if !ok return;
    
    log("\n====\nINTERPRETING:");
    ok = interpret_program(*ast);
    if !ok return;
}

using Basic  :: #import "Basic";
using String :: #import "String";
using F      :: #import "File";
using HT     :: #import "Hash_Table";
using FP     :: #import "Flat_Pool";
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

print_tagged_union :: (sb: *String_Builder, value: Any) {
    tag_type    : *Type_Info_Enum;
    tag_value   : int;
    union_type  : *Type_Info_Struct;
    union_value : *void;
    
    for (cast(*Type_Info_Struct)value.type).members if it.name == {
        case "as"; {
            assert(it.type.type == .STRUCT);
            union_type  = cast(*Type_Info_Struct) it.type;
            union_value = value.value_pointer + it.offset_in_bytes;
        }
        case "type"; {
            assert(it.type.type == .ENUM);
            tag_type  = cast(*Type_Info_Enum) it.type;
            tag_value = (cast(*int)(value.value_pointer + it.offset_in_bytes)).*;
        }
    }
    
    assert(union_type != null);
    assert(tag_type != null);
    assert(tag_value >= 0 && tag_value < tag_type.names.count, "Corrupt tag %", tag_value);
    
    a: Any = ---; a.type = tag_type; a.value_pointer = *tag_value;
    print_item_to_builder(sb, a);
    upper := tag_type.names[tag_value];
    lower := to_lower_copy(upper);
    for union_type.members if it.name == lower {
        a.type = it.type;
        a.value_pointer = union_value + it.offset_in_bytes;
        print_to_builder(sb, "(%)", a);
    }
}

print_tagged_union :: (sb: *String_Builder, u: $T) {
    print_item_to_builder(sb, u.type);
    #insert -> string { using QuickStringBuilder();
        ti_union := type_info(type_of(u.as));
        ti_enum  := type_info(type_of(u.type));
        P("if u.type == {\n");
        for ti_union.members {
            upper := to_upper_copy(it.name);
            if array_find(ti_enum.names, upper)
            then P("    case .%; print_to_builder(sb, \"(\%)\", w.as.%);\n", upper, it.name);
        }
        P("}\n");
        Return();
    }
}

// print_tagged_union :: (_sb: *String_Builder, w: $T) { #insert -> string {
//     sb: String_Builder;
//     append(*sb, "if w.type == {\n");
//     for type_info(type_of(w.as)).members {
//         upper := to_upper_copy(it.name);
//         if array_find(type_info(type_of(w.type)).names, upper) {
//             print_to_builder(*sb,
//                 "    case .%; print_to_builder(_sb, \"\%(\%)\", w.type, w.as.%);\n",
//                 upper, it.name
//             );
//         }
//     }
//     append(*sb, "    case; print_item_to_builder(_sb, w.type);\n}");
//     return builder_to_string(*sb);
// } }

// type array
//     ptr name(data)
//     int name(count)
// end

// type list
//     ptr name(data)
//     int name(count)
//     int name(capacity)
// end

// type file
//     int     name(fd)
//     u8 list name(contents)
// end

// push_var(my_tmp_list, int list)
// def tappend
//     dup(6) .count .capacity >= if
//         tmp_list_expand
//     end
//     .data .count offset rot !
//     .count 1 + !count
// end
// def tlist_initial_size() 256 end
// def tlist_expand
//     dup(3) .data null = if
//         dup tmp_list_initial_size talloc
//         rot !data !capacity drop(*)
//     else
//         .capacity 2 * dup(2) !capacity talloc
//         over(2) .data copy
//     end
// end
// type array(t)
//     t*  name(data)
//     int name(count)
// end
// type list(type)
//     type* name(data)
//     int   name(count)
//     int   name(capacity)
// end
// type string
//     addr name(data)
//     int  name(count)
// end
// type ivec3
//     int name(x)
//     int name(y)
//     int name(z)
// end
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
// tmp_get_mark defer tmp_set_mark end
// tmp_list var(found, list(entity*))
// ...
// found tmp_list_add

// var(vec, int name(x) int int name(z) int)
// 69  vec!x
// 420 vec!z

// push_var(buf, u8[256])
// push_var(len, u32)
    
// TODO: stack manipulation primitives
// dup  or dup(num > 0)
// rot  or rot(num > 0)
// over or over(num > 0)
// drop or drop(num > 0)