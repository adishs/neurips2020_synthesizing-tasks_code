from z3 import z3


from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block, single_block_change
from utils_ast_smt import ASTNode, remove_null_nodes



def generate_assignments(thresh = 2, id = 'karel'):

    # create the initial z3 solver
    solver = z3.Solver()
    # declare a block
    block_1 = {'b1_1': 'put_marker', 'b1_2': 'move', 'b1_3': 'turn_left'}

    block_1_obj = SMT_Block(block_1, thresh, id =id )

    values = block_1_obj.block_values

    c1 = z3.Int('c1')  # 4 (repeat)
    values.append(

        z3.Or(c1 == 3, c1 == 4, c1 == 5),

    )

    # declare a block
    block_2 = {'b2_1': 'phi'}

    block_2_obj = SMT_Block(block_2, thresh, id=id)

    values.extend(block_2_obj.block_values)

    # declare a block
    block_3 = {'b3_1': 'phi'}

    block_3_obj = SMT_Block(block_3, thresh, id=id)

    values.extend(block_3_obj.block_values)

    block_objs = [block_1_obj, block_2_obj, block_3_obj]

    # declare the values that each of the variables can take
    X = [ele.var for ele in block_1_obj.block_z3_vars]
    X.append(c1)
    X.extend([ele.var for ele in block_2_obj.block_z3_vars])
    X.extend([ele.var for ele in block_3_obj.block_z3_vars])


    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + \
                  block_1_obj.flip_marker_constraints + block_1_obj.block_elimination_constraints + \
                  block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + \
                  block_2_obj.flip_marker_constraints + block_2_obj.block_elimination_constraints + \
                  block_3_obj.block_append_constraints + block_3_obj.flip_turns_constraints + \
                  block_3_obj.flip_marker_constraints + block_3_obj.block_elimination_constraints


    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)

    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)
    assignments = []
    for model in models:
        a = [str(model[c1].as_long())]
        a.extend([type_to_str[VariableType(model[ele.var].as_long())]
            for ele in block_1_obj.block_z3_vars
             ])

        a.extend([type_to_str[VariableType(model[ele.var].as_long())]
                  for ele in block_2_obj.block_z3_vars
                  ])

        a.extend([type_to_str[VariableType(model[ele.var].as_long())]
                  for ele in block_3_obj.block_z3_vars
                  ])



        assignments.append(a)
        #print(a)



    #print('Found #{} SAT values'.format(len(models)))
    return assignments




def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:
        ast = ASTNode('run', None, [

            ASTNode(a[10]),  ASTNode(a[11]),
            ASTNode(a[12]),
            ASTNode(a[13]), ASTNode(a[14]),

            ASTNode('repeat', a[0], [
                ASTNode(a[1]), ASTNode(a[2]),
                ASTNode(a[3]),
                ASTNode(a[4]), ASTNode(a[5]), ASTNode(a[6]),
                ASTNode(a[7]),
                ASTNode(a[8]), ASTNode(a[9]),


            ]),


            ASTNode(a[15]), ASTNode(a[16]),
            ASTNode(a[17]),
            ASTNode(a[18]), ASTNode(a[19]),


        ])
        # remove the nodes which are phi'
        ast = remove_null_nodes(ast)

        ####### Allow asts with blocks of code NOT matching inner block of repeat
        if is_ast_repeat_valid(ast):
            all_ast_progs.append(ast)

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

    Karel_8 = ASTNode('run', None, [
        ASTNode('repeat', '4', [ASTNode('put_marker'), ASTNode('move'), ASTNode('turn_left')])]
                      )
    karel_8_json = Karel_8.to_json()
    print("Karel_8:", karel_8_json)

    return Karel_8


