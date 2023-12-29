import Pkg;
Pkg.add("DataStructures");
using DataStructures;
function read_from_file(file)
    lines = []
    open(file, "r") do f
        for i in readlines(f)
            push!(lines, i)
        end
    end
    return lines
end
function write_to_file(file, str)
    open(file, "w") do f
        print(f, str)
    end
end
struct Grammer
    grammar
    start_nterm
    nterms
    terms
end
mutable struct Rule
    left
    right
end
mutable struct Table
    rows
    cols
    table
end
struct Todo
    type::String
    data::Int
end

mutable struct TreeNode{T}
    status::Int
    path::String
    data::Vector{T}
    children::Vector{TreeNode}
    root::TreeNode
    TreeNode(data::Vector{T}) where T = new{T}(0, "0", data, TreeNode[])
end

function grammar_print(grammer)
    res = ""
    for rule ∈ grammer
        res *= rule.left*" ➡ "*join(rule.right)*"\n"
    end
    return res
end
function states_print(states)
    res = ""
    for (i, state) in enumerate(states)
        res *= "#State = $i\n"
        res *= "#begin\n"
        res *= grammar_print(state)
        res *= "#end\n"
    end
    return res
end

function parse_com_is_srt(lines)
    return parse(Bool, lines[begin])
end

function parse_input(lines)
    priority = false
    flag = C_NULL
    str = []
    for (index, line) ∈ enumerate(lines)
        if line == "#priority"
            flag = "priority"
        elseif line == "#string"
            flag = "string"
        elseif line == "#grammar"
            str = join(str, "\n")
            grammer, grammer¹ = parse_grammar(lines[index+1:end])
            return priority, str, grammer, grammer¹
        else
            if flag == "priority"
                priority = parse(Bool, line)
            elseif flag == "string"
                push!(str, line)
            end
        end
    end
end

function parse_grammar(lines)
    grammer¹ = []
    grammer = Dict()
    nterms = Set()
    terms = Set()
    start_nterm = "S"
    new_start_nterm = "S'"
    push!(grammer¹, Rule(new_start_nterm, [start_nterm]))
    for rule ∈ lines
        sub_g = split(rule, "➡")
        lr = strip(sub_g[1])
        push!(nterms, lr)
        rr = strip(sub_g[2])
        alters = split(rr, "|")
        rules = []
        for alter in alters
            chars = split(strip(alter))
            for i in chars
                push!(terms, i)
            end
            push!(rules, chars)
            push!(grammer¹, Rule(lr, [i for i in chars]))
        end
        grammer[lr] = sort(rules, by=length, rev=true)
    end
    setdiff!(terms, nterms)
    if "S" ∉ nterms
        println("В гламматике нет стартового символа")
    end
    while new_start_nterm ∈ nterms
        new_start_nterm*="'"
    end
    grammer¹[1].left = new_start_nterm
    grammer[new_start_nterm] = [[start_nterm]]
    return Grammer(grammer, new_start_nterm, nterms, terms), grammer¹
end
function compare_rules(rule¹, rule²)
    if rule¹.left != rule².left || rule¹.right != rule².right
        return false
    else
        return true
    end
end
function compare_states(state¹, state²)
    if length(state¹) != length(state²)
        return false
    else
        for i in eachindex(state¹)
            if !compare_rules(state¹[i], state²[i])
                return false
            end
        end
        return true
    end
end

function gotos_print(gotos)
    for key in sort(collect(keys(gotos)), by=x -> x[1])
        println("GOTO(I$(key[1]), $(key[2])) ➡ I$(gotos[key])")
    end
end
function todo_to_string(todo)
    if typeof(todo) == Vector{Todo}
        a = ""
        if length(todo) > 1
            for item in todo[1:length(todo)-1]
                a *= todo_to_string(item)*'/'
            end
            a *= todo_to_string(todo[end])
        else
            a = todo_to_string(todo[1])
        end
        return a
    elseif todo.type=="Shift"
        return "S$(todo.data)"
    elseif todo.type=="Reduse"
        return "R$(todo.data)"
    elseif todo.type=="Goto"
        return "G$(todo.data)"
    elseif todo.type == "Accept"
        return "FI"
    else
        return "  "
    end
end
function parse_table_print(table)
    println("\t"*join(table.cols, "\t"))
    for (index¹, row) ∈ enumerate(table.rows)
        println(string(row)*"\t"*join([todo_to_string(todo) for todo ∈ table.table[index¹]], "\t"))
    end
end

function find_closure(state, nterm, grammar, start_nterm)
    closure_set = []
    if nterm == start_nterm
        for rule in grammar
            if rule.left == start_nterm
                push!(closure_set, rule)
            end
        end
    else
        closure_set = state
    end
    count = -1

    while count != length(closure_set)
        count = length(closure_set)
        new_closure_set = []
        for rule in closure_set
            dot_index = findfirst(x -> x == ".", rule.right)
            if rule.right[end] != "."
                move_dot = rule.right[dot_index+1]
                for rule¹ ∈ grammar
                    if move_dot == rule¹.left && !(rule¹ ∈ new_closure_set)
                        push!(new_closure_set, rule¹)
                    end
                end
            end
        end
        for rule ∈ new_closure_set
            if !(rule ∈  closure_set)
                push!(closure_set, rule)
            end
        end
    end
    return closure_set
end

function find_goto!(state, states, gotos, start_nterm, grammar)
    states_for = []
    for rule in states[state]
        if rule.right[end] != "."
            dot_index = findfirst(x -> x == ".", rule.right)
            move_dot = rule.right[dot_index+1]
            if !(move_dot ∈ states_for)
                push!(states_for, move_dot)
            end
        end
    end
    if ! isempty(states_for)
        for symbol ∈ states_for
            goto!(state, symbol, states, gotos, start_nterm, grammar)
        end
    end
end

function goto!(state, symbol, states, gotos, start_nterm, grammar)
    new_state = []
    for rule ∈ states[state]
        dot_index = findfirst(x -> x == ".", rule.right)
        if rule.right[end] != "." && rule.right[dot_index+1] == symbol
            shift = deepcopy(rule)
            shift.right[dot_index], shift.right[dot_index+1] = shift.right[dot_index+1], shift.right[dot_index]
            push!(new_state, shift)
        end
    end
    closure = []
    for rule ∈ new_state
        dot_index = findfirst(x -> x == ".", rule.right)
        if rule.right[end] != "."
            res_closure = find_closure(new_state, rule.right[dot_index+1], grammar, start_nterm)
            for rule¹ ∈ res_closure
                if !(rule¹ ∈ closure) && !(rule¹ in new_state)
                    push!(closure, rule¹)
                end
            end
        end
    end
    for rule ∈ closure
        push!(new_state, rule)
    end
    required_state = 0
    for state in eachindex(states)
        if compare_states(states[state], new_state)
            required_state = state
            break
        end
    end
    if required_state == 0
        push!(states, new_state)
        gotos[(state, symbol)] = length(states)
    else
        gotos[(state, symbol)] = required_state
    end
end

function gen_states!(states, gotos, start_nterm, grammar)
    count = -1
    goto_for = []

    while length(states) != count
        count = length(states)
        for state ∈ eachindex(states)
            if !(state ∈ goto_for)
                push!(goto_for, state)
                find_goto!(state, states, gotos, start_nterm, grammar)
            end
        end
    end
end

function get_follow_set(output_path)
    follow_set = Dict{String, Any}()
    lines = read_from_file(output_path)
    follow_set["S'"] = ["Δ"];
    for line in lines
        term, c = eachsplit(line," ➡ ")
        if haskey(follow_set, term)
            push!(follow_set[term], c)
        else
            follow_set[term] = [c]
        end
    end
    return follow_set
end
function gen_table(states, gotos, terms, nterms, grammar¹, follow_set)
    rows = collect(eachindex(states))
    cols = [[term for term ∈ terms]; ["Δ"]; [nterm for nterm ∈ nterms]]
    todos = Vector{Vector{Vector{Todo}}}()
    for _ in rows
        push!(todos, Vector{Vector{Todo}}())
        for _ in cols
            push!(todos[end], Vector{}())
            push!(todos[end][end], Todo("Error", C_NULL))
        end
    end

    parse_table = Table(rows, cols, todos)
    for key in keys(gotos)
        state = key[1]
        symbol = key[2]
        symbol_index = findfirst(x -> x == symbol, parse_table.cols)
        parse_table.table[state][symbol_index][1] = ((symbol ∈ nterms) ? Todo("Goto", gotos[key]) : Todo("Shift", gotos[key]))
    end
    for (index, state) in enumerate(states)
        for rule in state
            if rule.right[end] == "."
                ndot_rule = Rule(rule.left, filter(x -> x != ".", rule.right))
                for (number, rule¹) ∈ enumerate(grammar¹)
                    if compare_rules(rule¹, ndot_rule)
                        for follow in follow_set[ndot_rule.left]
                            follow_index = findfirst(x -> x == follow, parse_table.cols)
                            if number == 1
                                parse_table.table[index][follow_index][1] = Todo("Accept", C_NULL)
                            else
                                if parse_table.table[index][follow_index][1].type == "Error"
                                    parse_table.table[index][follow_index][1] = Todo("Reduse", number)
                                else
                                    push!(parse_table.table[index][follow_index], Todo("Reduse", number))
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return parse_table
end

function run_ref(input_path, output_path)
    if Sys.iswindows()
        run(`./main.exe $input_path $output_path`)
    else
        run(`./main $input_path $output_path`)
    end
    return
end

function get_root(node::TreeNode)
    if isdefined(node, :root)
        return node.root
    else
        return nothing
    end
end

function parse_string(stack, flow, arrow, line, count,
                parse_table, states, grammar¹, grammar, follow_set, step, pos)
    global show
    while arrow <= length(flow)
        current_char = flow[arrow]
        if current_char == "\n"
            current_char = "\$"
        end
        if current_char == " "
            current_char = "_"
        end
        println("char $(current_char) stack $(stack.data) step $(step) pos $(pos) arrow $(arrow)")
        state = stack.data[end]g
        todo = [Todo("Error", C_NULL)]
        if current_char ∈ parse_table.cols
            todo = parse_table.table[state][findfirst(x -> x == current_char, parse_table.cols)]
        end
        if length(todo) == 1
            todo = todo[1]
            println(todo)
            if todo.type == "Error"
                stack.status = -1
                return
            elseif todo.type == "Accept"
                stack.status = 1
                return
            elseif todo.type == "Shift"
                step += 1
                push!(stack.data, todo.data)
            else
                step += 1

                rule = grammar¹[todo.data]
#                 println(stack.data, rule.right)
                if length(rule.right) >= length(stack.data)
                    parent = get_root(stack)
#                     println(parent)
                    if isnothing(parent)
                        println("Super stack error")
                        exit(0)
                    end
#                     println(parent.data, stack.data)
                    stack.data = vcat(parent.data, stack.data)
                    grand_parent = get_root(parent)
                    if !isnothing(grand_parent)
#                         println(grand_parent)
                        stack.root = grand_parent
                    end
                end
                for _ ∈ rule.right
                    pop!(stack.data)
                end
                state¹ = stack.data[end]
                push!(stack.data, parse_table.table[state¹][findfirst(x -> x == rule.left, parse_table.cols)][1].data)
                continue
            end
        else
            stack.status = 2
            global first_split
            if first_split == ""
                first_split = "Error in line $line col $(arrow-count) by term $(current_char)"
            end
            for item in todo
                next = 1
                node = TreeNode([])
                node.path = pos*'('*item.type[1]*string(item.data)*')'
                node.root = stack
                println(node.path)
                if item.type == "Error"
                    node.status = -1
                    return
                elseif item.type == "Accept"
                    node.status = 1
                    return
                elseif item.type == "Shift"
                    step += 1
                    if step ==
                    node.data = [item.data]
#                     println("Item $(item) Node $(node.data)")
                else
                    step += 1
                    rule = grammar¹[item.data]
                    node.data = stack.data
                    if length(rule.right) >= length(node.data)
                        parent = get_root(stack)
                        if isnothing(parent)
                            println("Super stack error")
                            exit(0)
                        end
                        node.data = vcat(parent.data, node.data)
                    end
                    for _ ∈ rule.right
                        pop!(node.data)
                    end
                    state¹ = node.data[end]
                    next = 0
                    push!(node.data, parse_table.table[state¹][findfirst(x -> x == rule.left, parse_table.cols)][1].data)
                end
                push!(stack.children, node)
                println(stack.children[end].path, node.path)
                parse_string(node, flow, arrow+next, line, count,
                    parse_table, states, grammar¹, grammar, follow_set, step,
                    node.path)
            end
            return
        end
        arrow+=1
        if current_char == "\$"
            line+=1
            count+=(arrow-count)-1
        end
    end
end


status = false
show = parse(Int32, ARGS[3])
first_split = ""
function process_tree(root, level=0, prnt=false)
    global status
    s = root.status
    status = s == 1
    if s == -1
        s = "Reject"
    elseif s == 1
        s = "Accept"
    elseif s == 2
        s = "Splitted"
    end
    if prnt
        println('\t'^level, root.data, " with status: $(s), path: $(root.path)")
    end
    if !isempty(root.children)
        for c in root.children
            process_tree(c, level+1)
        end
    end
    return
end

begin
    input_path = ARGS[1]
    output_path = ARGS[2]
    run_ref(input_path, output_path)
    priority, str, grammar, grammar¹ = parse_input(read_from_file(ARGS[1]))
    dot_grammar = [Rule(rule.left, [["."]; rule.right]) for rule ∈ grammar¹]
    states = []
    gotos = Dict()
    push!(states, find_closure(C_NULL, dot_grammar[1].left, dot_grammar, dot_grammar[1].left))
    gen_states!(states, gotos, dot_grammar[1].left, dot_grammar)
    follow_set = get_follow_set(output_path)
    println(follow_set)
    table = gen_table(states, gotos, grammar.terms, grammar.nterms, grammar¹, follow_set)
    parse_table_print(table);
    str *= "Δ"
    flow = split(str, "")
    arrow = 1
    line = 1
    count = 0
    step = 1
    pos = "0"
    christmas_tree = TreeNode([1])
    parse_string(christmas_tree, flow, arrow, line, count,
        table, states, grammar¹, grammar, follow_set, step, pos)
    process_tree(christmas_tree, 0, false)
    global status
    if !status
        println(first_split)
    else
        println("Accepted")
    end
end