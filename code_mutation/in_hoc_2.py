from z3 import z3

from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block, single_block_change
from utils_ast_smt import ASTNode, remove_null_nodes, is_last_child_turn


def generate_assignments(thresh = 2):

    solver = z3.Solver()
    # declare the SMT variables for the specific code
    block_1 = {'b1_1': 'turn_right'}
    block_1_obj = SMT_Block(block_1, thresh)
    values =  block_1_obj.block_values

    c1 = z3.Int('c1') # 5 (repeat)
    values.append(

        z3.Or(c1 == 4, c1 == 5, c1 == 6),

    )

    block_2 = {'b2_1': 'move'}
    block_2_obj = SMT_Block(block_2, thresh)
    values.extend(block_2_obj.block_values)

    # additional empty block added in the end of the code
    block_3 = {'b3_1': 'phi'}
    block_3_obj = SMT_Block(block_3, thresh)
    values.extend(block_3_obj.block_values)

    # all block objects
    block_objs = [block_1_obj, block_2_obj, block_3_obj]


    X = [ele.var for ele in block_1_obj.block_z3_vars] # added the variables for block 1
    X.append(c1) # added the conditional variable
    X.extend([ele.var for ele in block_2_obj.block_z3_vars]) # added the variables for block 2


    block_3_vars = [ele.var for ele in block_3_obj.block_z3_vars]
    X.extend(block_3_vars)  # added the variables for block 3


    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.block_elimination_constraints  \
                  + block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + block_2_obj.block_elimination_constraints \
                  + block_3_obj.block_append_constraints + block_3_obj.flip_turns_constraints + block_3_obj.block_elimination_constraints



    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)


    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)
    assignments = []
    for model in models:
        a = [type_to_str[VariableType(model[ele].as_long())]
             for ele in X[:block_1_obj.size]]
        a.append(str(model[c1].as_long()))

        b = [
             type_to_str[VariableType(model[ele].as_long())]
            for ele in X[block_2_obj.size+1:]

             ]
        a.extend(b)

        c = [
             type_to_str[VariableType(model[ele].as_long())]
            for ele in block_3_vars

             ]
        a.extend(c)
        assignments.append(a)
        #print(a)

    #print('Found #{} SAT values'.format(len(models)))
    return assignments


def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:
        ast = ASTNode('run', None, [

            ASTNode(a[0]), ASTNode(a[1]), ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]),

            ASTNode('repeat', a[5], [

                ASTNode(a[6]), ASTNode(a[7]), ASTNode(a[8]), ASTNode(a[9]), ASTNode(a[10])
            ]),

            ASTNode(a[11]), ASTNode(a[12]), ASTNode(a[13]), ASTNode(a[14]), ASTNode(a[15])

        ])

        ast = remove_null_nodes(ast)

        ##### remove the asts with turn actions in the end
        if not is_last_child_turn(ast):
            ######## Remove the asts with blocks matching the block inside repeat
            if is_ast_repeat_valid(ast):
                all_ast_progs.append(ast)
        ####################################################

    return all_ast_progs



def is_ast_repeat_valid(ast: ASTNode):

    root_children = ast.children()
    repeat_children = []

    for ele in root_children:
        if ele._type == "repeat":
            repeat_children.extend(ele.children())

    repeat_children_types = [ele._type for ele in repeat_children]
    if len(repeat_children_types) == 0:
        print("No elements inside repeat")
        return False

    if len(repeat_children_types) >1:
        flag = all(ele == "move" for ele in repeat_children_types)
        if flag:
            return False

    children_types  = [ele._type for ele in root_children]

    id_of_repeat = children_types.index('repeat')

    block_1 = children_types[:id_of_repeat]
    block_2 = children_types[id_of_repeat + 1:]

    if repeat_children_types == block_1[-len(repeat_children_types):]: #end ele
        return False
    if repeat_children_types == block_2[:len(repeat_children_types)]: #first ele
        return False


    return True






def get_p_star():

    HOC_2 = ASTNode('run', None, [ASTNode('turn_right'),
                                  ASTNode('repeat', '5', [ASTNode('move')])]
                    )
    hoc_2_json = HOC_2.to_json()
    print("HOC_2:", hoc_2_json)
    return HOC_2


