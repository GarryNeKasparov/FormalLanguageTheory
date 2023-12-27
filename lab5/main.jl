
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
    data::Int64
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
function gen_com_for_is_srl(states, follow_set)
    res = "#for\ni\n#states\n"*states_print(states)
    res *= "#follow\n"
    for nterm ∈ keys(follow_set)
        res *= "#Nterm = $nterm\n"
        res *= "#begin\n"
        for terms ∈ follow_set[nterm]
            res *= terms*"\n"
        end
        res *= "#end\n"
    end
    return res
end
function gen_com_for_panic(arrow, line, counter, str, state, paths, follow_set, priority)
    res = "#for\np\n#priority\n$priority\n#arrow\n"*string(arrow)*"\n"*"#line\n"*string(line)*"\n"*"#counter\n"*string(counter)*"\n"*"#string\n"*str*"\n"
    res *= "#state\n"*grammar_print(state)*"#paths\n"
    for path in paths
        res *= "#begin\n"
        for nterm ∈ path
            res *= nterm*"\n"
        end
        res *= "#end\n"
    end
    res *= "#follow\n"
    for nterm ∈ keys(follow_set)
        res *= "#Nterm = $nterm\n"
        res *= "#begin\n"
        for terms ∈ follow_set[nterm]
            res *= terms*"\n"
        end
        res *= "#end\n"
    end
    return res
end
function parse_com_is_srt(lines)
    return parse(Bool, lines[begin])
end
function parse_com_for_panic(lines)
    flag = C_NULL
    arrow = C_NULL
    lin = C_NULL
    count = C_NULL
    nterm = C_NULL
    drop = C_NULL
    for line ∈ lines
        if line == "#arrow"
            flag = "arrow"
        elseif line == "#line"
            flag = "line"
        elseif line == "#counter"
            flag = "counter"
        elseif line == "#nterm"
            flag = "nterm"
        elseif line == "#drop"
            flag = "drop"
        else
            if flag == "arrow"
                arrow = parse(Int, line)
            elseif flag == "line"
                lin = parse(Int, line)
            elseif flag == "counter"
                count = parse(Int, line)
            elseif flag == "nterm"
                nterm = line
            elseif flag == "drop"
                drop = parse(Int, line)
            end
        end
    end
    return arrow, lin, count, nterm, drop
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
        elseif line == "#grammer"
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
function compute_order¹(grammar, view, nterm)
    paths = []
    for alter ∈ grammar.grammar[nterm]
        for symbol ∈ alter
            if symbol ∈ grammar.nterms && symbol ∉ view
                rec_paths = compute_order¹(grammar, [view; symbol], symbol)
                if isempty(rec_paths)
                    push!(paths, symbol)
                end
                for path ∈ rec_paths
                    push!(paths, [[symbol]; path])
                end
            end
        end
    end
    return paths
end

function compute_order(grammar)
    paths = compute_order¹(grammar, [grammar.start_nterm], grammar.start_nterm)
    paths = [[[grammar.start_nterm]; path] for path ∈ paths]
    unique!(paths)
#     TODO Vlad
    function is_older(nterm¹, nterm²)
        for path ∈ paths
            if nterm² ∈ path
                nterm_index = findfirst(x -> x == nterm², path)
                if nterm¹ ∉ path[begin:nterm_index]
                    return false
                end
            end
        end
        return true
    end
    return paths
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
function gen_first(rule, grammar, marked)
    if !isempty(rule)
        if rule[1] ∈ grammar.terms
            return Set([rule[1]])
        elseif rule[1] == "ϵ"
            return Set(["ϵ"])
        end
        if rule[1] ∈ grammar.nterms
            push!(marked, rule[1])
            res = Set()
            alter = grammar.grammar[rule[1]]

            for rule¹ ∈ alter
                marked¹ = copy(marked)
                if rule¹[1] ∉ marked¹
                    first_for = gen_first(rule¹, grammar, marked¹)
                    for f_term ∈ first_for
                        push!(res, f_term)
                    end
                end
            end
            if "ϵ" ∉ res
                return res
            else
                new_res = Set()
                filter!(x -> x != "ϵ", res)
                if length(rule) > 1
                    marked¹ = copy(marked)
                    if rule[2:end] ∉ marked¹
                        new_first = first(rule[2:end])
                        if new_first != false
                            new_res = res ∪ new_first
                        else
                            new_res = Set(res)
                        end
                        return new_res
                    end
                end
                push!(res, "ϵ")
                return res
            end
        else
            return false
        end
    else
        return false
    end
end
function gen_follow(nterm, grammar)
    follow = Set()
    if nterm == grammar.start_nterm
        push!(follow, "Δ")
    end
    for current ∈ keys(grammar.grammar)
        right_rules = grammar.grammar[current]
        for sub_rule ∈ right_rules
            if nterm ∈ sub_rule
                while nterm ∈ sub_rule
                    nterm_index = findfirst(x -> x == nterm, sub_rule)
                    sub_rule = sub_rule[nterm_index+1:end]
                    res = C_NULL
                    if !isempty(sub_rule)
                        res = gen_first(sub_rule, grammar, [])
                        if "ϵ" ∈ res
                            filter!(x -> x != "ϵ", res)
                            current_follow = gen_follow(current, grammar)
                            res = res ∪ current_follow
                        end
                    else
                        if nterm != current
                            res = gen_follow(current, grammar)
                        end
                    end
#                     println(res, nterm)
                    if res != false && res != C_NULL
                        for i ∈ res
                            push!(follow, i)
                        end
                    end
                end
            end
        end
    end
    return follow
end
function create_follow_set(grammar)
    follow_set = Dict()
    for nterm in keys(grammar.grammar)
        follow_set[nterm] = gen_follow(nterm, grammar)
    end
    return follow_set
end
function gen_table(states, gotos, terms, nterms, grammar¹, follow_set)
    rows = collect(eachindex(states))
    cols = [[term for term ∈ terms]; ["Δ"]; [nterm for nterm ∈ nterms]]
#     a = [[Todo("Error", C_NULL)], [Todo("Error", C_NULL), Todo("Lol", C_NULL)]]
    todos = Vector{Vector{Vector{Todo}}}()
    for _ in rows
#         push!(todos, [Todo("Error", C_NULL) for _ in cols])
        tmp = Vector{Vector{Todo}}()
        push!(todos, tmp)
        for _ in cols
            push!(todos[end], Vector{}())
#             println(todos[end][end], Todo("Error", C_NULL))
            push!(todos[end][end], Todo("Error", C_NULL))
        end
#         println(todos[length(todos)])
    end
#     push!(todos[1][1], Todo("PO", C_NULL))
#     println(todos[1][1])
#     exit(1)
#     parse_table = Table(rows, cols, [[Todo("Error", C_NULL) for _ in cols] for _ in rows])
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
#     println(parse_table)
    return parse_table
end
# TODO Vlad
# function bubble_sort(vector, is_older)
#     swapped = true
#     while swapped
#         swapped = false
#         for i in 1:length(vector)-1
#             if is_older(vector[i], vector[i + 1])
#                 vector[i], vector[i + 1] = vector[i + 1], vector[i]
#                 swapped = true
#             end
#         end
#     end
# end
macro run_ref()
    return :(Sys.iswindows() ? run(`main.exe ./com.txt ./com.txt`) : run(`./main ./com.txt ./com.txt`))
end
function parse_string(str, parse_table, states, grammar¹, paths, grammar, follow_set, priority)
    str *= "Δ"
    stack = []
    push!(stack, 1)
    flow = split(str, "")
    arrow = 1
    panic = false
    line = 1
    count = 0
    while arrow <= length(flow)
        current_char = flow[arrow]
        if current_char == "\n"
            current_char = "\$"
        end
        if current_char == " "
            current_char = "_"
        end
        if false
            # TODO Vlad
            # state = stack[end]
            # get = []
            # for nterm ∈ [rule.left for rule ∈ states[state]]
            #     if current_char ∈ follow_set[nterm]
            #         push!(get, nterm)
            #     end
            # end
            # unique!(get)
            # if !isempty(get)
            #     bubble_sort(get, is_older)
            #     used = C_NULL
            #     if priority
            #         right = sort([rule.right[begin:findfirst(x -> x == ".", rule.right)-1] for rule ∈ filter(x -> x.left == get[begin], states[state])], by=length)
            #         used = Rule(get[begin], right[begin])
            #     else
            #         right = sort([rule.right[begin:findfirst(x -> x == ".", rule.right)-1] for rule ∈ filter(x -> x.left == get[end], states[state])], by=length)
            #         used = Rule(get[end], right[end])
            #     end
            #     TODO I is my part
            #     for _ ∈ used.right
            #         pop!(stack)
            #     end
            #     state¹ = stack[end]
            #     push!(stack, parse_table.table[state¹][findfirst(x -> x == used.left, parse_table.cols)].data)
            #     panic = false
            #     continue
            # end
        else
            state = stack[end]
            todo = Todo("Error", C_NULL)
            if current_char ∈ parse_table.cols
                todo = parse_table.table[state][findfirst(x -> x == current_char, parse_table.cols)]
            end
            if todo.type == "Error"
                println("Error as line $line col $(arrow-count) by term $(current_char)")
                if arrow >= length(flow)
                    @goto accept
                end
                write_to_file("com.txt", gen_com_for_panic(arrow, line, count, str, states[state], paths, follow_set, priority))
                try
                    @run_ref
                catch _
                    arrow = length(flow)
                    @goto accept
                end
                arrow, line, count, nterm, drop = parse_com_for_panic(read_from_file("com.txt"))
                if arrow > length(flow)
                    @goto accept
                end
                for _ ∈ 1:drop
                    pop!(stack)
                end
                state¹ = stack[end]
                push!(stack, parse_table.table[state¹][findfirst(x -> x == nterm, parse_table.cols)].data)
                panic = false
                continue

            elseif todo.type == "Shift"
                push!(stack, todo.data)
            elseif todo.type == "Accept"
                @label accept
                println("Accepted")
            else
                rule = grammar¹[todo.data]
                for _ ∈ rule.right
                    pop!(stack)
                end
                state¹ = stack[end]
                push!(stack, parse_table.table[state¹][findfirst(x -> x == rule.left, parse_table.cols)].data)
                continue
            end
        end
        arrow+=1
        if current_char == "\$"
            line+=1
            count+=(arrow-count)-1
        end
    end
end


begin
    priority, str, grammar, grammar¹ = parse_input(read_from_file(ARGS[1]))
    paths = compute_order(grammar)
    dot_grammar = [Rule(rule.left, [["."]; rule.right]) for rule ∈ grammar¹]
    states = []
    gotos = Dict()
    push!(states, find_closure(C_NULL, dot_grammar[1].left, dot_grammar, dot_grammar[1].left))
    gen_states!(states, gotos, dot_grammar[1].left, dot_grammar)
#     follow_set = create_follow_set(grammar)
    follow_set = Dict("S'" => Set(["Δ"]), "S" => Set(["Δ", "a"]), "A" => Set(["Δ", "a"]))
    println(follow_set)
    table = gen_table(states, gotos, grammar.terms, grammar.nterms, grammar¹, follow_set)
    parse_table_print(table);
#     parse_string(str, table, states, grammar¹, paths, grammar, follow_set, priority)

end