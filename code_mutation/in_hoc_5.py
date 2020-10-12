from z3 import z3


from utils_smt import VariableType, ConditionalType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block, single_block_change
from utils_ast_smt import ASTNode, remove_null_nodes


def generate_assignments(thresh = 2):

    solver = z3.Solver()
    # Block 1
    block_1 = {'b1_1': 'move'}
    block_1_obj = SMT_Block(block_1, thresh)
    values = block_1_obj.block_values
    block_1_vars = [ele.var for ele in block_1_obj.block_z3_vars] # for the conditional constraints


    c1 = z3.Int('c1')  # bool_path_left (if_only)
    values.append(z3.Or(c1 == 8, c1 == 9))

    block_2 = {'b2_1': 'turn_left'}
    block_2_obj = SMT_Block(block_2, thresh)
    values.extend(block_2_obj.block_values)
    block_2_vars = [ele.var for ele in block_2_obj.block_z3_vars] # for the conditional constraints

    block_3 = {'b3_1': 'phi'}
    block_3_obj = SMT_Block(block_3, thresh)
    values.extend(block_3_obj.block_values)
    block_3_vars = [ele.var for ele in block_3_obj.block_z3_vars]  # for the conditional constraints

    # all block objects
    block_objs = [block_1_obj, block_2_obj, block_3_obj]

    X = [ele.var for ele in block_1_obj.block_z3_vars]  # added the variables for block 1
    X.append(c1)  # added the conditional variable
    X.extend([ele.var for ele in block_2_obj.block_z3_vars])  # added the variables for block 2
    X.extend([ele.var for ele in block_3_obj.block_z3_vars])  # added the variables for block 3

    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.block_elimination_constraints + \
                  block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + block_2_obj.block_elimination_constraints + \
                  block_3_obj.block_append_constraints + block_3_obj.flip_turns_constraints + block_3_obj.block_elimination_constraints


    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)

    constraints.extend([

        # conditional constraints: if(path_left)
        z3.Implies(c1 == 8, z3.Or(block_2_vars[0] == 2, block_2_vars[1] == 2,
                                  block_2_vars[2] == 2, block_2_vars[3] == 2,
                                  block_2_vars[4] == 2,

                                  )),
        z3.Implies(z3.And(c1 == 8, block_2_vars[1] == 2, block_2_vars[0] != 2), z3.And(block_2_vars[0] != 1, block_2_vars[0] != 3 )),
        z3.Implies(z3.And(c1 == 8, block_2_vars[2] == 2, block_2_vars[0] != 2, block_2_vars[1] != 2),
                   z3.And(block_2_vars[0] != 1, block_2_vars[0] != 3, block_2_vars[1] != 1, block_2_vars[1] != 3)),
        z3.Implies(z3.And(c1 == 8, block_2_vars[3] == 2, block_2_vars[0] != 2,
                          block_2_vars[1] != 2, block_2_vars[2] != 2), z3.And(block_2_vars[0] != 1, block_2_vars[0] != 3, block_2_vars[1] != 1, \
                                                                 block_2_vars[1] != 3, block_2_vars[2] != 1, block_2_vars[2] != 3)),
        z3.Implies(z3.And(c1 == 8, block_2_vars[4] == 2, block_2_vars[0] != 2,
                          block_2_vars[1] != 2, block_2_vars[2] != 2, block_2_vars[3] != 2), z3.And(block_2_vars[0] != 1, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 1, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 1, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 1, block_2_vars[3] != 3)),



        # conditional constraints: if(path_right)
        z3.Implies(c1 == 9, z3.Or(block_2_vars[0] == 3, block_2_vars[1] == 3,
                                  block_2_vars[2] == 3, block_2_vars[3] == 3,
                                  block_2_vars[4] == 3,

                                  )),
        z3.Implies(z3.And(c1 == 9, block_2_vars[1] == 3, block_2_vars[0] != 3,
                          ), z3.And(block_2_vars[0] != 1, block_2_vars[0] != 2)),
        z3.Implies(z3.And(c1 == 9, block_2_vars[2] == 3, block_2_vars[0] != 3,
                          block_2_vars[1] != 3), z3.And(block_2_vars[0]!= 1, block_2_vars[0] != 2,
                                                                 block_2_vars[1] != 1, block_2_vars[1] != 2)),
        z3.Implies(z3.And(c1 == 9, block_2_vars[3] == 3, block_2_vars[0] != 3,
                          block_2_vars[1] != 3, block_2_vars[2] != 3),
                   z3.And(block_2_vars[0] != 1, block_2_vars[0] != 2,
                          block_2_vars[1] != 1, block_2_vars[1] != 2,
                          block_2_vars[2] != 1, block_2_vars[2] != 2)),
        z3.Implies(z3.And(c1 == 9, block_2_vars[4] == 3, block_2_vars[0] != 3,
                          block_2_vars[1] != 3, block_2_vars[2] != 3, block_2_vars[3] != 3 ),
                   z3.And(block_2_vars[0] != 1, block_2_vars[0] != 2,
                          block_2_vars[1] != 1, block_2_vars[1] != 2,
                          block_2_vars[2] != 1, block_2_vars[2] != 2,
                          block_2_vars[3] != 1, block_2_vars[3] != 2)),

    ])

    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)
    assignments = []
    for model in models:
        a = ['repeat_until_goal(bool_goal)']
        a.extend([type_to_str[VariableType(model[ele].as_long())] for ele in X[:block_1_obj.size]])


        a.append(type_to_str[ConditionalType(model[c1].as_long())])

        a.extend([type_to_str[VariableType(model[ele].as_long())] for ele in X[block_1_obj.size+1:]
             ])

        a.extend([type_to_str[VariableType(model[ele].as_long())] for ele in block_3_vars
                  ])
        assignments.append(a)
        #print(a)

    #print('Found #{} SAT values'.format(len(models)))
    return assignments


def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:
        ast = ASTNode('run', None, [

           ASTNode(a[12]), ASTNode(a[13]), ASTNode(a[14]), ASTNode(a[15]), ASTNode(a[16]),

           ASTNode('repeat_until_goal', 'bool_goal', [
               ASTNode(a[1]), ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]), ASTNode(a[5]),

               ASTNode('if', a[6], [
                   ASTNode('do', a[6], [

                       ASTNode(a[7]), ASTNode(a[8]), ASTNode(a[9]), ASTNode(a[10]), ASTNode(a[11])

                   ])
               ])
           ])
        ])

        ast = remove_null_nodes(ast)
        all_ast_progs.append(ast)


    return all_ast_progs

def get_p_star():

    HOC_5 = ASTNode('run', None, [ASTNode('repeat_until_goal', 'bool_goal',
                                          [ASTNode('move'),
                                           ASTNode('if', 'bool_path_left',
                                                   [ASTNode('do', 'bool_path_left', [ASTNode('turn_left')])])])
                                  ])
    hoc_5_json = HOC_5.to_json()
    print("HOC_5:", hoc_5_json)

    return HOC_5

