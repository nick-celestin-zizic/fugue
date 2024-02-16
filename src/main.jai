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

FONT_DATA       :: #run cast([]u8) read_entire_file("firacode.ttf");
LIST_FONT_SCALE :: 0.025;
DATA_FONT_SCALE :: 0.035;

window_width         := 800;
window_height        := 600;
scroll_value         := 0.0;
theme                := #run Get_Rect.default_overall_theme;
list_font            := cast(*Simp.Dynamic_Font) null;
data_font            := cast(*Simp.Dynamic_Font) null;
variable_data_window := Get_Rect.Subwindow_Info.{};
init_my_fonts :: () {
    w := cast(float) window_width;
    h := cast(float) window_height;
    m := min(w, h);
    
    list_font = Simp.get_font_at_size(FONT_DATA, cast(int)(m*LIST_FONT_SCALE));
    assert(list_font != null);
    data_font = Simp.get_font_at_size(FONT_DATA, cast(int)(m*DATA_FONT_SCALE));
    assert(data_font != null);
    
    s := .5*m;
    variable_data_window.rect = .{ w - 1.5*s, h - s, 1.5*s, s };
}

render_value :: (sb: *String_Builder, desc: Type_Stack_Item, memory: *void) {
    v := memory + desc.offset;
    if #complete desc.type.type == {
        case .ADR; #through;
        case .PTR; print_to_builder(sb, "0x% ", (cast(**void)v).*);
        case .BUL; append(sb, ifx (cast(*int)v).* == 0 then "false " else "true ");
        case .NUM; print_to_builder(sb, "% ", (cast(*int)v).*);
        case .STK; for desc.type.as.stk render_value(sb, .{
            it.type, ifx desc.name then tprint("%.%", desc.name, it.name) else it.name,
            desc.offset + it.offset
        }, memory);
        case .BUF; assert(false, "TODO");
        case .NAME; assert(false);
        case; assert(false);
    }
    if desc.name && desc.type.type != .STK
    then print_to_builder(sb, "name(%) ", desc.name);
}

inspector: struct {
    active := false;
    item   := Type_Stack_Item.{};
}

// Debug_Info :: struct {
//     ip     : int;     // current instruction
//     tape   : []FWord; // procedure being debugged
//     setup  : []FWord; // metaprogram that sets up VM state
//     dict   : FDict;
//     vars   : []Type_Stack_Item;
//     stacks : [][]*FType; // stacks[ip] is the type stack AFTER tape[i] executes
// }
// load_program :: (path: string) -> Debug_Info, bool {
p: Pool;
load_program :: (path: string) -> Virtual_Machine, Program, Typer, bool {
    reset(*p);
    p.block_allocator = context.allocator;
    PushState(context.allocator, .{pool_allocator_proc, *p});
    
    src, ok := read_entire_file(path);
    if !ok return .{}, .{}, .{}, false;
    ast:, ok = parse(src);
    if !ok return .{}, .{}, .{}, false;
    types:, ok = typecheck_program(*ast);
    if !ok return .{}, .{}, .{}, false;
    
    vm: Virtual_Machine;
    remember_allocators(*vm.bindings);
    if !interpret_words(*vm, *ast.words, ast.loose) return .{}, .{}, .{}, false;
    return vm, ast, types, true;
}

// UA :: #import "Unmapping_Allocator";
main :: () {
    // context.allocator = UA.get_unmapping_allocator();
    context.print_style.default_format_struct.use_long_form_if_more_than_this_many_members = 3;
    context.print_style.struct_printer = my_struct_printer;
    args := get_command_line_arguments(,, temp);
    if args.count != 2 {
        log_error("usage: % <input path>", args[0]);
        return;
    }
    
    vm, ast, types, ok := load_program(args[1]);
    main_body:, ok = table_find(*ast.words, "main");
    assert(ok);
    type_stack: []*FType;
    ip := 0;
    Step :: () #expand {
        type_stack = types.stacks[ip];
        ip = interpret_word(*vm, *ast.words, ip, main_body);
        assert(ip > 0);
        if ip >= main_body.count {
            inspector.active = false;
            type_stack = .[];
            ip = 0;
            vm = .{bindings.allocator=.{pool_allocator_proc, *p}};
            ok = interpret_words(*vm, *ast.words, ast.loose);
            assert(ok);
        }
    }
    
    window := Window_Creation.create_window(window_width, window_height, "Fugue");
    Simp.set_render_target(window);
    _, _, window_width, window_height = Window_Creation.get_dimensions(window, true);
    Get_Rect.ui_init();
    init_my_fonts();
    theme.label_theme.font = list_font;
    
    draw_variable_window_capture := Tuple(*Virtual_Machine, *Typer).{*vm, *types};
    draw_variable_window :: (_r: Get_Rect.Rect, data: *void) {
        using cast(*type_of(draw_variable_window_capture)) data;
        vm := _0; tp := _1;
        
        PushState(theme.label_theme.alignment, .Left);
        PushState(theme.label_theme.font, data_font);
        PushState(context.print_style.default_format_int, .{
            base=16, minimum_digits=2
        });
        PushState(context.print_style.default_format_array, .{
            separator=" ", begin_string="", end_string="",
            stop_printing_after_this_many_elements = -1
        });
        
        CHUNK_SIZE :: 16;
        buf: [CHUNK_SIZE]u8; memset(buf.data, 0xff, buf.count);
        r   := _r;
        r.h  = window_height*DATA_FONT_SCALE;
        r.y += r.h;
        r.w  = xx Simp.prepare_text(data_font, tprint(" % ", buf));
        r.x += (_r.w-r.w) * .5;
        
        if inspector.active {
            sb := String_Builder.{allocator=temp};
            render_value(*sb, inspector.item, vm.vars.data);
            text := builder_to_string(*sb,, temp);
            PushState(theme.button_theme.font, list_font);
            Get_Rect.button(.{_r.x, r.y, _r.w, r.h}, text, *theme.button_theme);
            r.y += r.h*2;
        }
        
        variables: [..]Type_Stack_Item; variables.allocator = temp;
        for tp.global_scope array_add(*variables, it);
        for tp.local_scope.bindings if it.offset < vm.vars_top then array_add(*variables, it);
        for variables {
            rect := r;
            PushState(theme.button_theme.surface_color,
                ifx inspector.active && (inspector.item.offset == it.offset)
                then .{.08, .08, .32, 1.0} else theme.button_theme.surface_color
            );
            Btn :: (loc := #caller_location) #expand {
                if Get_Rect.button(rect, "", *theme.button_theme, it.offset, loc = loc) {
                    inspector.active = true;
                    inspector.item   = it;
                }
            }
            
            assert(it.type != null);
            s := runtime_size(it.type);
            m := cast(float) (it.offset%CHUNK_SIZE);
            if (it.offset/CHUNK_SIZE) == ((it.offset+s-1)/CHUNK_SIZE) {
                rect.w *= cast(float)s/CHUNK_SIZE;
                rect.x += rect.w*(m/CHUNK_SIZE)*(CHUNK_SIZE/8);
                rect.y += rect.h*(it.offset/CHUNK_SIZE);
                Btn();
            } else { // item spans multiple rows
                // first partial button
                rect.w *= (CHUNK_SIZE-m)/CHUNK_SIZE;
                rect.x += rect.w*(m/CHUNK_SIZE)*2;
                rect.y += rect.h*(it.offset/CHUNK_SIZE);
                Btn();
                
                // full row buttons
                d := (CHUNK_SIZE-(it.offset%CHUNK_SIZE));
                o := it.offset + d;
                l := s - d;
                rect.w = r.w;
                while l >= CHUNK_SIZE {
                    rect.y += rect.h;
                    Btn();
                    o += CHUNK_SIZE;
                    l -= CHUNK_SIZE;
                }
                
                // last partial button
                if l {
                    rect.w *= (cast(float)l/CHUNK_SIZE);
                    rect.x  = r.x;
                    rect.y  = r.y + (rect.h * (cast(float)o/CHUNK_SIZE));
                    Btn();
                }
            }
        }
        
        vars: []u8 = .{vm.vars_top, vm.vars.data};
        w, i := 0, 0;
        while vars {
            line: []u8 = .{min(CHUNK_SIZE, vars.count), vars.data};
            if !line break;
            Get_Rect.label(r, tprint("%", line), *theme.label_theme);
            i   += 1;
            r.y += r.h;
            vars.data  += line.count;
            vars.count -= line.count;
        }
    }
    
    variable_data_window.draw       = draw_variable_window;
    variable_data_window.user_data  = *draw_variable_window_capture;
    variable_data_window.title_text = "Variables";
    
    current_time : float64;
    last_time    : float64;
    quit := false;
    while !quit {
        reset_temporary_storage();
        current_time = seconds_since_init();
        dt := cast(float)(current_time - last_time);
        Clamp(*dt, 0, 0.1);
        last_time = current_time;

        Input.update_window_events();
        for Input.get_window_resizes() {
            Simp.update_window(it.window);
            if it.window == window {
                window_width  = it.width;
                window_height = it.height;
                if (it.width != window_width) || (it.height != window_height)
                then init_my_fonts();  // Resize the font for the new window size.
            }
        }
        
        for Input.events_this_frame {
            Get_Rect.getrect_handle_event(it);
            assert(!it.files);
            if it.type == {
            case .QUIT; quit = true;
            case .KEYBOARD; if it.key_pressed && it.key_code == #char " " then Step();
            case .DRAG_AND_DROP_FILES; assert(false, "%", it.files);
            }
        }
        
        Simp.clear_render_target(.1, .1, .1, 1);
        x, y, w, h := Window_Creation.get_dimensions(window, true);
        Get_Rect.ui_per_frame_update(window, w, h, current_time);
        k := window_height * .01;
        
        r: Get_Rect.Rect;
        {
            using Get_Rect;
            r = .{k, 5*k, window_width*.5-2*k, window_height-10*k};
            region, inside := begin_scrollable_region(r);
            button_height  := floor(window_height*DATA_FONT_SCALE);
            s   := inside;
            s.h  = button_height;
            s.y -= scroll_value;
            defer end_scrollable_region(region, s.x + s.w, s.y + s.h, *scroll_value);
            
            PushState(theme.button_theme.font, data_font);
            PushState(theme.button_theme.alignment, .Left);
            for main_body {
                text := tprint("[%] %", FormatInt.{value=it_index, minimum_digits=2}, it);
                PushState(theme.button_theme.text_color,
                    ifx it_index == ip then .{.1, .6, .1, 1} else theme.button_theme.text_color
                );
                
                if   button(s, text, *theme.button_theme, it_index)
                then while ip != it_index Step();
                
                if   it_index != main_body.count-1
                then s.y += floor(button_height * 1.1 + 0.5);
            }
        }
        
        {
            using Get_Rect;
            r.x += r.w + k;
            r.h  = 5*k;
            PushState(theme.label_theme.font, list_font);
            PushState(theme.label_theme.alignment, .Left);
            
            { // register stack
                regs: []int = .{vm.regs_top, xx vm.regs.data};
                sb := String_Builder.{allocator=temp};
                append(*sb, "Register Stack: ");
                for 0..vm.regs_top-1 {
                    item := Type_Stack_Item.{type_stack[it], "", cast(u32) it*size_of(int)};
                    render_value(*sb, item, regs.data);
                }
                str := builder_to_string(*sb,, temp);
                label(r, str, *theme.label_theme);
            }
            
            if variable_data_window.open {
                state := add_subwindow(*variable_data_window, *theme.subwindow_theme);
            }
            
            // TODO: dynamic memory pages
            
            { // program output
                r.y += r.h+k*.5;
                output := builder_to_string(*vm.output, do_reset = false,, temp);
                label(r, tprint("Output:"), *theme.label_theme);
                
                r.y += r.h*.75;
                found, line, rhs := String.split_from_left(output, #char "\n");
                while found {
                    output = rhs;
                    label(r, line, *theme.label_theme);
                    r.y += r.h*.75;
                    found, line, rhs = String.split_from_left(output, #char "\n");
                }
                if output then label(r, output, *theme.label_theme);
            }
        }
        
        Get_Rect.draw_popups();
        Simp.swap_buffers(window);
        sleep_milliseconds(10);
    }
    
    // destroy_heap(heap);
    release(*p);
    log("Temporary Storage High Water Mark: % bytes", context.temporary_storage.high_water_mark);
    log("\nMemory Leak Report:");
    report_memory_leaks(.{
        known_allocation_leaves = .[
            .{"New", "Basic"}, .{"NewArray", "Basic"},
            .{"array_add", "Basic"}, .{"table_add", "Hash_Table"},
            .{"copy_string", "Basic"}, .{"alloc_string", "Basic"}
        ]
    });
}

using Basic  :: #import "Basic"()(MEMORY_DEBUGGER=true);
using Math   :: #import "Math";
using String :: #import "String";
using Sort   :: #import "Sort";
using F  :: #import "File";
using HT :: #import "Hash_Table";
using P  :: #import "Pool";
using BA :: #import "Bucket_Array";
Window_Creation :: #import "Window_Creation";
Simp            :: #import "Simp";
Input           :: #import "Input";
Get_Rect        :: #import "GetRect_LeftHanded";
#load "parser.jai";
#load "interpreter.jai";
#load "typer.jai";

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
        assert(num >= 0, "corrupt tag %", num);
        assert(num < val_type.members.count, "corrupt tag %", num);
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