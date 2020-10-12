from z3 import z3


from utils_smt import VariableType, ConditionalType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block, block_unequal_constraint, single_block_change
from utils_ast_smt import ASTNode, remove_null_nodes


def generate_assignments(thresh = 2, id = 'karel'):
    solver = z3.Solver()
    # declare the SMT variables for the specific code
    # Block 1
    c0 = z3.Int('c0') # repeat (8)
    c1 = z3.Int('c1')  # bool_no_marker (if_else)

    block_1 = {'b1_1': 'put_marker'}
    block_1_obj = SMT_Block(block_1, thresh, id = id)
    values = block_1_obj.block_values
    block_1_vars = [ele.var for ele in block_1_obj.block_z3_vars]  # for the conditional constraints


    block_2 = {'b2_1': 'pick_marker'}
    block_2_obj = SMT_Block(block_2, thresh, id = id)
    values.extend(block_2_obj.block_values)
    block_2_vars = [ele.var for ele in block_2_obj.block_z3_vars] # for the conditional constraints

    values.append(z3.Or(c0 == 7, c0 == 8, c0 == 9))
    values.append(z3.Or(c1 == 10, c1 == 11)) # bool_no_marker, bool_marker


    block_3 = {'b3_1': 'move'}
    block_3_obj = SMT_Block(block_3, thresh, id=id)
    values.extend(block_3_obj.block_values)
    block_3_vars = [ele.var for ele in block_3_obj.block_z3_vars]  # for the conditional constraints

    block_4 = {'b4_1': 'phi'}
    block_4_obj = SMT_Block(block_4, thresh, id=id)
    values.extend(block_4_obj.block_values)
    block_4_vars = [ele.var for ele in block_4_obj.block_z3_vars]  # for the conditional constraints

    block_5 = {'b5_1': 'phi'}
    block_5_obj = SMT_Block(block_5, thresh, id=id)
    values.extend(block_5_obj.block_values)
    block_5_vars = [ele.var for ele in block_5_obj.block_z3_vars]  # for the conditional constraints



    # all block objects
    block_objs = [block_1_obj, block_2_obj, block_3_obj, block_4_obj, block_5_obj]

    X = [c0,c1]
    X.extend([ele.var for ele in block_1_obj.block_z3_vars] ) # added the variables for block 1
    X.extend([ele.var for ele in block_2_obj.block_z3_vars])  # added the variables for block 2
    X.extend([ele.var for ele in block_3_obj.block_z3_vars])  # added the variables for block 3
    X.extend([ele.var for ele in block_4_obj.block_z3_vars])  # added the variables for block 4
    X.extend([ele.var for ele in block_5_obj.block_z3_vars])  # added the variables for block 5



    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.flip_marker_constraints+ \
                  block_1_obj.block_elimination_constraints + \
                  block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + \
                  block_2_obj.flip_marker_constraints+block_2_obj.block_elimination_constraints + \
                  block_3_obj.block_append_constraints + block_3_obj.flip_turns_constraints + \
                  block_3_obj.flip_marker_constraints+block_3_obj.block_elimination_constraints + \
                  block_4_obj.block_append_constraints + block_4_obj.flip_turns_constraints + \
                  block_4_obj.flip_marker_constraints + block_4_obj.block_elimination_constraints + \
                  block_5_obj.block_append_constraints + block_5_obj.flip_turns_constraints + \
                  block_5_obj.flip_marker_constraints + block_5_obj.block_elimination_constraints


    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)

    constraints.extend([

        # conditional constraints: if_else(bool_no_marker)---if block constraints
        z3.Implies(c1 == 11, block_1_vars[0] != 4),
        z3.Implies(z3.And(c1 == 11, block_1_vars[1] == 4, block_1_vars[0] != 4), z3.Or(block_1_vars[0] == 1, block_1_vars[0] == 5)),
        z3.Implies(z3.And(c1 == 11, block_1_vars[2] == 4,
                          block_1_vars[0] != 4, block_1_vars[1] != 4), z3.Or(block_1_vars[0] == 1, block_1_vars[0] == 5,
                                                                block_1_vars[1] == 1, block_1_vars[1] == 5)),

        z3.Implies(z3.And(c1 == 11, block_1_vars[3] == 4,
                          block_1_vars[0] != 4, block_1_vars[1] != 4,
                          block_1_vars[2] != 4),
                   z3.Or(block_1_vars[0] == 1, block_1_vars[0] == 5,
                         block_1_vars[1] == 1, block_1_vars[1] == 5,
                         block_1_vars[2] == 1, block_1_vars[2] == 5)),
        z3.Implies(z3.And(c1 == 11, block_1_vars[4] == 4,
                          block_1_vars[0] != 4, block_1_vars[1] != 4,
                          block_1_vars[2] != 4,  block_1_vars[3] != 4
                          ),
                   z3.And(block_1_vars[0] == 1, block_1_vars[0] == 5,
                          block_1_vars[1] == 1, block_1_vars[1] == 5,
                          block_1_vars[2] == 1, block_1_vars[2] == 5,
                          block_1_vars[3] == 1, block_1_vars[3] == 5)),



        # else block constraints
        z3.Implies(c1 == 11, block_2_vars[0] != 5),
        z3.Implies(z3.And(c1 == 11, block_2_vars[1] == 5, block_2_vars[0] != 5), z3.Or(block_2_vars[0] == 1, block_2_vars[0] == 4)),
        z3.Implies(z3.And(c1 == 11, block_2_vars[2] == 5,
                          block_2_vars[0] !=5 , block_2_vars[1] != 5), z3.Or(block_2_vars[0] == 1, block_2_vars[0] == 4,
                                                                 block_2_vars[1] == 1, block_2_vars[1] == 4)),



        z3.Implies(z3.And(c1 == 11, block_2_vars[3] == 5,
                          block_2_vars[0] !=5 , block_2_vars[1] != 5,
                          block_2_vars[2] != 5),
                   z3.Or(block_2_vars[0] == 1, block_2_vars[0] == 4,
                         block_2_vars[1] == 1, block_2_vars[1] == 4,
                         block_2_vars[2] == 1, block_2_vars[2] == 4)),
        z3.Implies(z3.And(c1 == 11, block_2_vars[4] == 5,
                          block_2_vars[0] != 5, block_2_vars[1] != 5,
                          block_2_vars[2] != 5, block_2_vars[3] != 5
                          ),
                   z3.And(block_2_vars[0] == 1, block_2_vars[0] == 4,
                          block_2_vars[1] == 1, block_2_vars[1] == 4,
                          block_2_vars[2] == 1, block_2_vars[2] == 4,
                          block_2_vars[3] == 1, block_2_vars[3] == 4)),



        # conditional constraints: if_else(bool_marker)---if block constraints
        z3.Implies(c1 == 10, block_1_vars[0] != 5),
        z3.Implies(z3.And(c1 == 10, block_1_vars[1] == 5, block_1_vars[0] != 5), z3.Or(block_1_vars[0] == 1, block_1_vars[0] == 4)),
        z3.Implies(z3.And(c1 == 10, block_1_vars[2] == 5,
                          block_1_vars[0] != 5, block_1_vars[1] != 5), z3.Or(block_1_vars[0] == 1, block_1_vars[0] == 4,
                                                                 block_1_vars[1] == 1, block_1_vars[1] == 4)),

        z3.Implies(z3.And(c1 == 10, block_1_vars[3] == 5,
                          block_1_vars[0] != 5, block_1_vars[1] != 5,
                          block_1_vars[2] != 5),
                   z3.Or(block_1_vars[0] == 1, block_1_vars[0] == 4,
                         block_1_vars[1] == 1, block_1_vars[1] == 4,
                         block_1_vars[2] == 1, block_1_vars[2] == 4)),
        z3.Implies(z3.And(c1 == 10, block_1_vars[4] == 5,
                          block_1_vars[0] != 5, block_1_vars[1] != 5,
                          block_1_vars[2] != 5, block_1_vars[3] != 5
                          ),
                   z3.And(block_1_vars[0] == 1, block_1_vars[0] == 4,
                          block_1_vars[1] == 1, block_1_vars[1] == 4,
                          block_1_vars[2] == 1, block_1_vars[2] == 4,
                          block_1_vars[3] == 1, block_1_vars[3] == 4)),




        # else block constraints
        z3.Implies(c1 == 10, block_2_vars[0] != 4),
        z3.Implies(z3.And(c1 == 10, block_2_vars[1] == 4,
                          block_2_vars[0] != 4), z3.Or(block_2_vars[0] == 1, block_2_vars[0] == 5)),
        z3.Implies(z3.And(c1 == 10, block_2_vars[2] == 4,
                          block_2_vars[0] != 4, block_2_vars[1] != 4), z3.Or(block_2_vars[0] == 1, block_2_vars[0] == 5,
                                                                 block_2_vars[1] == 1, block_2_vars[1] == 5)),

        z3.Implies(z3.And(c1 == 10, block_2_vars[3] == 4,
                          block_2_vars[0] != 4, block_2_vars[1] != 4,
                          block_2_vars[2] != 4),
                   z3.Or(block_2_vars[0] == 1, block_2_vars[0] == 5,
                         block_2_vars[1] == 1, block_2_vars[1] == 5,
                         block_2_vars[2] == 1, block_2_vars[2] == 5)),
        z3.Implies(z3.And(c1 == 10, block_2_vars[4] == 4,
                          block_2_vars[0] != 4, block_2_vars[1] != 4,
                          block_2_vars[2] != 4, block_2_vars[3] != 4
                          ),
                   z3.And(block_2_vars[0] == 1, block_2_vars[0] == 5,
                          block_2_vars[1] == 1, block_2_vars[1] == 5,
                          block_2_vars[2] == 1, block_2_vars[2] == 5,
                          block_2_vars[3] == 1, block_2_vars[3] == 5)),







    ])

    unequal_blocks_con = block_unequal_constraint(block_1_obj, block_2_obj)
    constraints.extend(unequal_blocks_con)
    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)

    assignments = []
    for model in models:
        a = [str(model[c0].as_long()),
             type_to_str[ConditionalType(model[c1].as_long())]]

        a.extend([type_to_str[VariableType(model[ele].as_long())]
             for ele in block_1_vars])

        a.extend([type_to_str[VariableType(model[ele].as_long())]
             for ele in block_2_vars

             ])
        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_3_vars

                  ])
        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_4_vars

                  ])
        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_5_vars

                  ])


        assignments.append(a)
        #print(a)

    #print('Found #{} SAT values'.format(len(models)))
    return assignments




def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:
        ast = ASTNode('run', None, [


            ASTNode(a[17]), ASTNode(a[18]),
            ASTNode(a[19]),
            ASTNode(a[20]), ASTNode(a[21]),


           ASTNode('repeat', a[0], [
               ASTNode('ifelse', a[1], [
                   ASTNode('do', a[1], [
                       ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]),

                       ASTNode(a[5]), ASTNode(a[6]),

                   ]),
                   ASTNode('else', a[1], [

                       ASTNode(a[7]), ASTNode(a[8]),
                       ASTNode(a[9]),
                       ASTNode(a[10]), ASTNode(a[11]),


                   ])
               ]),

               ASTNode(a[12]), ASTNode(a[13]),
               ASTNode(a[14]),
               ASTNode(a[15]), ASTNode(a[16]),

           ]),

            ASTNode(a[22]), ASTNode(a[23]),
            ASTNode(a[24]),
            ASTNode(a[25]), ASTNode(a[26]),

        ])

        ast = remove_null_nodes(ast)
        all_ast_progs.append(ast)



    return all_ast_progs




def get_p_star():

    Karel_9 = ASTNode('run', None, [
        ASTNode('repeat', '8', [
            ASTNode('ifelse', 'bool_no_marker', [
                ASTNode('do', 'bool_no_marker', [ASTNode('put_marker')]),
                ASTNode('else', 'bool_no_marker', [ASTNode('pick_marker')])
            ]),
            ASTNode('move')
        ])
    ])
    karel_9_json = Karel_9.to_json()
    print("Karel_9:", karel_9_json)

    return Karel_9