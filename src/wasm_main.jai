#program_export "get_return_register"
get_return_register :: () -> *void #c_call { return xx *return_space; }
return_space: U128; // 16 byte so that we can fit strings and stuff

#run,host {
    #import "Compiler";
    #load "parser.jai";
    #load "typer.jai";
    #load "interpreter.jai";
    #load "common.jai"; 
    context.print_style.default_format_struct.use_long_form_if_more_than_this_many_members = -1;
    context.print_style.default_format_struct.draw_type_name  = true;
    context.print_style.default_format_struct.use_newlines_if_long_form = true;
    context.print_style.default_format_array.stop_printing_after_this_many_elements = -1;
    context.print_style.struct_printer = my_struct_printer;
    
    convert :: #bake_arguments replace(old="<br>", new="\n");
    run :: (src: string) {
        err := load(src);
        if err
        then log("ERROR: %\n%", convert(err), context.fugue_state.main_body);
        else log("===== OUTPUT START\n%\n===== OUTPUT END", convert(context.fugue_state.final_output));
        reset(*context.fugue_state.memory);
        mem := context.fugue_state.memory;
        context.fugue_state = .{memory = mem};
    }
    
    run(#string __python
    def putln "<br>" puts end
    def main
        10 var(width)
        0 while dup width. < do
            putln
            0 while dup over(2) < do
                "*" puts
                1 +
            end
            while dup width. < do
                "." puts
                1 +
            end drop
            1 +
        end drop
    end
    __python);
}

/*
def main
	0 while dup(2) 10 < do
		0 while dup over(2) < do
			"*" puts
			1 +
		end drop(2)
		"<br>" puts
		1 +
	end drop(2)
end
*/

step :: () {
    using context.fugue_state;
    if ip >= main_body.count {
        ip  = 0;
        vm  = .{bindings.allocator=.{pool_allocator_proc, *memory}};
        ok := interpret_words(*vm, *prog.words, prog.loose);
        assert(ok);
    } else {
        ip = interpret_word(*vm, *prog.words, ip, main_body);
        assert(ip >= 0);
    }
}

get_fugue_state :: () -> string {
    using context.fugue_state;
    PushState(context.allocator, temp);
    
    sb: String_Builder;
    append(*sb, "{\n");
    
    append(*sb, "  \"registers\": [");
    current_stack := ifx ip then stacks[ip-1] else .[];
    for 0..regs_top-1 {
        item := Type_Stack_Item.{current_stack[it], "", cast(u32) it*size_of(int)};
        render_value(*sb, item, regs.data);
        if it != regs_top-1 then append(*sb, ",");
    }
    append(*sb, "],\n");
    
    variables: [..]Type_Stack_Item;
    for global_scope array_add(*variables, it);
    for local_scope.bindings if it.offset < vars_top then array_add(*variables, it);
    append(*sb, "  \"variables\": {\n");
    for variables print(*sb, #string _js
    "%": {
      "size": %,
      "offset": %,
      "value": "%"
    }%
        _js, it.name, runtime_size(it.type), it.offset,
        Format_Fugue_Value.{it, vars.data, false},
        ifx it_index != variables.count-1 then "," else ""
    );
    append(*sb, "\n  },\n");
    
    {
        PushState(context.print_style.default_format_int, .{
            base=16, minimum_digits=2
        });
        PushState(context.print_style.default_format_array, .{
            separator=" ", begin_string="", end_string="",
            stop_printing_after_this_many_elements = -1
        });
        vs: []u8 = .{vars_top, vars.data};
        print(*sb, "    \"variable_buffer\": \"%\",\n", vs);
    }
    
    PushState(context.print_style.default_format_array, .{
        separator="\", \"", begin_string="[\"", end_string="\"]",
        stop_printing_after_this_many_elements = -1
    });
    print(*sb, #string _js
  "main": %,
  "ip": %,
  "final_output": "%",
  "current_output": "%"
        _js,
        main_body, ip, final_output,
        builder_to_string(*output, do_reset = false)
    );
    
    append(*sb, "}");
    str := builder_to_string(*sb);
    // log(str);
    return str;
}

main :: ()  {
    assert(false, "don't call main, this is a library!");
    // procs called here are so that they do not get removed by dead code elimination
    reset_temporary_storage();
    get_return_register();
    talloc(0);
}

make_string :: (count: int, data: *void) -> *void {
    str      := New(string, initialized=false,, temp);
    str.count = count;
    str.data  = data;
    return str;
}

#scope_module
#import "Basic";
#import "String";
#import "Hash_Table";
#import "Pool";
#import "Sort";
#import "Print_Vars";
#load "parser.jai";
#load "typer.jai";
#load "interpreter.jai";
#load "common.jai";
