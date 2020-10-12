from z3 import z3


from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block, single_block_change
from utils_ast_smt import ASTNode, remove_null_nodes, is_last_child_turn


def generate_assignments(thresh = 2):

    solver = z3.Solver()
    # declare the SMT variables for the specific code
    block_1 = {'b1_1': 'move'}
    block_1_obj = SMT_Block(block_1, thresh)
    values =  block_1_obj.block_values
    block_1_vars = [ele.var for ele in block_1_obj.block_z3_vars]  # for the conditional constraints



    c1 = z3.Int('c1') # 4 (repeat)
    values.append(

        z3.Or(c1 == 3, c1 == 4, c1 == 5),

    )


    block_2 = {'b2_1': 'turn_left'}
    block_2_obj = SMT_Block(block_2, thresh)
    values.extend(block_2_obj.block_values)
    block_2_vars = [ele.var for ele in block_2_obj.block_z3_vars]  # for the conditional constraints

    c2 = z3.Int('c2')  # 5 (repeat)
    values.append(

        z3.Or(c2 == 4, c2 == 5, c2 == 6),

    )

    block_3 = {'b3_1': 'move'}
    block_3_obj = SMT_Block(block_3, thresh)
    values.extend(block_3_obj.block_values)
    block_3_vars = [ele.var for ele in block_3_obj.block_z3_vars]  # for the conditional constraints

    # add another block in the beginning of the code
    block_4 = {'b4_1': 'phi'}
    block_4_obj = SMT_Block(block_4, thresh)
    values.extend(block_4_obj.block_values)
    block_4_vars = [ele.var for ele in block_4_obj.block_z3_vars]

    # add another block in the end of the code
    block_5 = {'b5_1': 'phi'}
    block_5_obj = SMT_Block(block_5, thresh)
    values.extend(block_5_obj.block_values)
    block_5_vars = [ele.var for ele in block_5_obj.block_z3_vars]


    # all block objects
    block_objs = [block_1_obj, block_2_obj, block_3_obj, block_4_obj, block_5_obj]


    X = [ele.var for ele in block_1_obj.block_z3_vars] # added the variables for block 1
    X.append(c1) # added the conditional variable
    X.extend([ele.var for ele in block_2_obj.block_z3_vars]) # added the variables for block 2
    X.append(c2)  # added the conditional variable
    X.extend([ele.var for ele in block_3_obj.block_z3_vars])  # added the variables for block 3

    X.extend([ele.var for ele in block_4_obj.block_z3_vars])  # added the variables for block 4
    X.extend([ele.var for ele in block_5_obj.block_z3_vars])  # added the variables for block 5


    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.block_elimination_constraints + \
                  block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + block_2_obj.block_elimination_constraints + \
                  block_3_obj.block_append_constraints + block_3_obj.flip_turns_constraints + block_3_obj.block_elimination_constraints + \
                  block_4_obj.block_append_constraints + block_4_obj.flip_turns_constraints + block_4_obj.block_elimination_constraints + \
                  block_5_obj.block_append_constraints + block_5_obj.flip_turns_constraints + block_5_obj.block_elimination_constraints




    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)



    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)
    assignments = []
    for model in models:


        a = [str(model[c1].as_long())]
        a.extend([type_to_str[VariableType(model[ele].as_long())]
             for ele in block_1_vars])

        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_2_vars])

        a.append(str(model[c2].as_long()))

        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_3_vars])

        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_4_vars])

        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_5_vars])



        assignments.append(a)
        #print(a)

    #print('Found #{} SAT values'.format(len(models)))
    return assignments


def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:
        ast = ASTNode('run', None, [

            ASTNode(a[17]), ASTNode(a[18]), ASTNode(a[19]), ASTNode(a[20]), ASTNode(a[21]),
            ASTNode('repeat', a[0], [
                ASTNode(a[1]), ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]), ASTNode(a[5])
            ]),

            ASTNode(a[6]), ASTNode(a[7]), ASTNode(a[8]), ASTNode(a[9]), ASTNode(a[10]),
            ASTNode('repeat', a[11], [
                ASTNode(a[12]), ASTNode(a[13]), ASTNode(a[14]), ASTNode(a[15]), ASTNode(a[16])
            ]),

            ASTNode(a[22]), ASTNode(a[23]), ASTNode(a[24]), ASTNode(a[25]), ASTNode(a[26])

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

    repeat_indices = [i for i, x in enumerate(root_children) if x._type == "repeat"]
    if len(repeat_indices) == 0:
        print("No repeat encountered")
        return True

    children_types = [ele._type for ele in root_children]

    #### Assumption: Code has only 2 repeat constructs
    repeat_1_children = [ele._type for ele in root_children[repeat_indices[0]].children()]
    repeat_2_children = [ele._type for ele in root_children[repeat_indices[1]].children()]

    if len(repeat_1_children) == 0:
        print("No elements inside repeat")
        return False

    if len(repeat_2_children) == 0:
        print("No elements inside repeat")
        return False

    if len(repeat_1_children) >1:
        flag = all(ele == "move" for ele in repeat_1_children)
        if flag:
            return False

    if len(repeat_2_children) > 1:
        flag = all(ele == "move" for ele in repeat_2_children)
        if flag:
            return False


    block_1 = children_types[:repeat_indices[0]]
    block_2 = children_types[repeat_indices[0]+1:repeat_indices[1]]
    block_3 = children_types[repeat_indices[1]+1:]

    # print(block_1, block_2, block_3)
    # print(repeat_1_children, repeat_2_children)

    if repeat_1_children == block_1[-len(repeat_1_children):]: #end ele
        return False
    if repeat_1_children == block_2[:len(repeat_1_children)]: #first ele
        return False
    if repeat_2_children == block_2[-len(repeat_2_children):]: #end ele
        return False
    if repeat_2_children == block_3[:len(repeat_2_children)]: #first ele
        return False

    return True







def get_p_star():

    HOC_3 = ASTNode('run', None, [
        ASTNode('repeat', '4', [ASTNode('move')]),
        ASTNode('turn_left'),
        ASTNode('repeat', '5', [ASTNode('move')])]
                    )
    hoc_3_json = HOC_3.to_json()
    print("HOC_3:", hoc_3_json)

    return HOC_3


