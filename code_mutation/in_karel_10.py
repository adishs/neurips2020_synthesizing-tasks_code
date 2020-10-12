from z3 import z3


from utils_smt import VariableType, ConditionalType, str_to_type, gen_model, gen_all, type_to_str
from utils_block_smt import SMT_Block, single_block_change, block_unequal_constraint
from utils_ast_smt import ASTNode, remove_null_nodes



def generate_assignments(thresh = 2, id = 'karel'):
    solver = z3.Solver()
    # declare the SMT variables for the specific code
    # Block 1


    block_1 = {'b1_1': 'put_marker'}
    block_1_obj = SMT_Block(block_1, thresh, id = id)
    values = block_1_obj.block_values
    block_1_vars = [ele.var for ele in block_1_obj.block_z3_vars]  # for the conditional constraints

    c1 = z3.Int('c1')  # bool_path_ahead (while)
    values.append(z3.Or(c1 == 7, c1 == 12))  # bool_path_ahead, bool_no_path_ahead

    block_2 = {'b2_1': 'move', 'b2_2': 'turn_left', 'b2_3': 'move', 'b2_4': 'turn_right', 'b2_5': 'put_marker'}
    block_2_obj = SMT_Block(block_2, thresh, id = id)
    values.extend(block_2_obj.block_values)
    block_2_vars = [ele.var for ele in block_2_obj.block_z3_vars] # for the conditional constraints

    block_3 = {'b3_1': 'phi'}
    block_3_obj = SMT_Block(block_3, thresh, id=id)
    values.extend(block_3_obj.block_values)
    block_3_vars = [ele.var for ele in block_3_obj.block_z3_vars]  # for the conditional constraints

    # all block objects
    block_objs = [block_1_obj, block_2_obj, block_3_obj]

    X = [c1]
    X.extend([ele.var for ele in block_1_obj.block_z3_vars] ) # added the variables for block 1
    X.extend([ele.var for ele in block_2_obj.block_z3_vars])  # added the variables for block 2
    X.extend([ele.var for ele in block_3_obj.block_z3_vars])  # added the variables for block 3



    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.flip_marker_constraints+ \
                  block_1_obj.block_elimination_constraints + \
                  block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + \
                  block_2_obj.flip_marker_constraints + block_2_obj.block_elimination_constraints +\
                  block_3_obj.block_append_constraints + block_3_obj.flip_turns_constraints + \
                  block_3_obj.flip_marker_constraints + block_3_obj.block_elimination_constraints

    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)

    constraints.extend([

        # conditional constraints: while(bool_path_ahead)---while block constraints
        z3.Implies(c1 == 7,
                   z3.Or(block_2_vars[0] == 1, block_2_vars[1] == 1, block_2_vars[2] == 1, block_2_vars[3] == 1,
                         block_2_vars[4] == 1,
                         block_2_vars[5] == 1,
                         block_2_vars[6] == 1, block_2_vars[7] == 1,
                         block_2_vars[8] == 1,
                         block_2_vars[9] == 1, block_2_vars[10] == 1,

                         block_2_vars[11] == 1,
                         block_2_vars[12] == 1,

                         )),
        z3.Implies(z3.And(c1 == 7, block_2_vars[1] == 1, block_2_vars[0] != 1), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[2] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[3] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[4] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[5] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3,
                                                                 block_2_vars[4] != 2, block_2_vars[4] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[6] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3,
                                                                 block_2_vars[4] != 2, block_2_vars[4] != 3,
                                                                 block_2_vars[5] != 2, block_2_vars[5] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[7] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3,
                                                                 block_2_vars[4] != 2, block_2_vars[4] != 3,
                                                                 block_2_vars[5] != 2, block_2_vars[5] != 3,
                                                                 block_2_vars[6] != 2, block_2_vars[6] != 3)),
        z3.Implies(z3.And(c1 == 7, block_2_vars[8] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3,
                                                                 block_2_vars[4] != 2, block_2_vars[4] != 3,
                                                                 block_2_vars[5] != 2, block_2_vars[5] != 3,
                                                                 block_2_vars[6] != 2, block_2_vars[6] != 3,
                                                                 block_2_vars[7] != 2, block_2_vars[7] != 3)),



        z3.Implies(z3.And(c1 == 7, block_2_vars[9] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3,
                                                                 block_2_vars[4] != 2, block_2_vars[4] != 3,
                                                                 block_2_vars[5] != 2, block_2_vars[5] != 3,
                                                                 block_2_vars[6] != 2, block_2_vars[6] != 3,
                                                                 block_2_vars[7] != 2, block_2_vars[7] != 3,
                                                                 block_2_vars[8] != 2, block_2_vars[8] != 3)),

        z3.Implies(z3.And(c1 == 7, block_2_vars[10] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1, block_2_vars[9] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                                                 block_2_vars[1] != 2, block_2_vars[1] != 3,
                                                                 block_2_vars[2] != 2, block_2_vars[2] != 3,
                                                                 block_2_vars[3] != 2, block_2_vars[3] != 3,
                                                                 block_2_vars[4] != 2, block_2_vars[4] != 3,
                                                                 block_2_vars[5] != 2, block_2_vars[5] != 3,
                                                                 block_2_vars[6] != 2, block_2_vars[6] != 3,
                                                                 block_2_vars[7] != 2, block_2_vars[7] != 3,
                                                                 block_2_vars[8] != 2, block_2_vars[8] != 3,
                                                                 block_2_vars[9] != 2, block_2_vars[9] != 3)),

        # # ################################################ THRESH = 2

        z3.Implies(z3.And(c1 == 7, block_2_vars[11] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1, block_2_vars[9] != 1,
                          block_2_vars[10] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                    block_2_vars[1] != 2, block_2_vars[1] != 3,
                                    block_2_vars[2] != 2, block_2_vars[2] != 3,
                                    block_2_vars[3] != 2, block_2_vars[3] != 3,
                                    block_2_vars[4] != 2, block_2_vars[4] != 3,
                                    block_2_vars[5] != 2, block_2_vars[5] != 3,
                                    block_2_vars[6] != 2, block_2_vars[6] != 3,
                                    block_2_vars[7] != 2, block_2_vars[7] != 3,
                                    block_2_vars[8] != 2, block_2_vars[8] != 3,
                                    block_2_vars[9] != 2, block_2_vars[9] != 3,
                                    block_2_vars[10] != 2, block_2_vars[10] != 3)),

        z3.Implies(z3.And(c1 == 7, block_2_vars[12] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1, block_2_vars[9] != 1,
                          block_2_vars[10] != 1,  block_2_vars[11] != 1
                          ), z3.And(block_2_vars[0] != 2, block_2_vars[0] != 3,
                                    block_2_vars[1] != 2, block_2_vars[1] != 3,
                                    block_2_vars[2] != 2, block_2_vars[2] != 3,
                                    block_2_vars[3] != 2, block_2_vars[3] != 3,
                                    block_2_vars[4] != 2, block_2_vars[4] != 3,
                                    block_2_vars[5] != 2, block_2_vars[5] != 3,
                                    block_2_vars[6] != 2, block_2_vars[6] != 3,
                                    block_2_vars[7] != 2, block_2_vars[7] != 3,
                                    block_2_vars[8] != 2, block_2_vars[8] != 3,
                                    block_2_vars[9] != 2, block_2_vars[9] != 3,
                                    block_2_vars[10] != 2, block_2_vars[10] != 3,
                                    block_2_vars[11] != 2, block_2_vars[11] != 3
                                    )),

        # # conditional constraints: while(bool_no_path_ahead)---while block constraints
        z3.Implies(c1 == 12, block_2_vars[0] != 1),
        z3.Implies(z3.And(c1 == 12, block_2_vars[1] == 1, block_2_vars[0] != 1), z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[2] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1), z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                                                               block_2_vars[1] == 2, block_2_vars[1] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[3] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                          block_2_vars[1] == 2, block_2_vars[1] == 3,
                          block_2_vars[2] == 2, block_2_vars[2] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[4] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1
                          ),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                          block_2_vars[1] == 2, block_2_vars[1] == 3,
                          block_2_vars[2] == 2, block_2_vars[2] == 3,
                          block_2_vars[3] == 2, block_2_vars[3] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[5] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1
                          ),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                          block_2_vars[1] == 2, block_2_vars[1] == 3,
                          block_2_vars[2] == 2, block_2_vars[2] == 3,
                          block_2_vars[3] == 2, block_2_vars[3] == 3,
                          block_2_vars[4] == 2, block_2_vars[4] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[6] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1
                          ),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                          block_2_vars[1] == 2, block_2_vars[1] == 3,
                          block_2_vars[2] == 2, block_2_vars[2] == 3,
                          block_2_vars[3] == 2, block_2_vars[3] == 3,
                          block_2_vars[4] == 2, block_2_vars[4] == 3,
                          block_2_vars[5] == 2, block_2_vars[5] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[7] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1
                          ),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                          block_2_vars[1] == 2, block_2_vars[1] == 3,
                          block_2_vars[2] == 2, block_2_vars[2] == 3,
                          block_2_vars[3] == 2, block_2_vars[3] == 3,
                          block_2_vars[4] == 2, block_2_vars[4] == 3,
                          block_2_vars[5] == 2, block_2_vars[5] == 3,
                          block_2_vars[6] == 2, block_2_vars[6] == 3)),
        z3.Implies(z3.And(c1 == 12, block_2_vars[8] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1
                          ),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                          block_2_vars[1] == 2, block_2_vars[1] == 3,
                          block_2_vars[2] == 2, block_2_vars[2] == 3,
                          block_2_vars[3] == 2, block_2_vars[3] == 3,
                          block_2_vars[4] == 2, block_2_vars[4] == 3,
                          block_2_vars[5] == 2, block_2_vars[5] == 3,
                          block_2_vars[6] == 2, block_2_vars[6] == 3,
                          block_2_vars[7] == 2, block_2_vars[7] == 3
                          )),


        z3.Implies(z3.And(c1 == 12, block_2_vars[9] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1
                          ),
                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                         block_2_vars[1] == 2, block_2_vars[1] == 3,
                         block_2_vars[2] == 2, block_2_vars[2] == 3,
                         block_2_vars[3] == 2, block_2_vars[3] == 3,
                         block_2_vars[4] == 2, block_2_vars[4] == 3,
                         block_2_vars[5] == 2, block_2_vars[5] == 3,
                         block_2_vars[6] == 2, block_2_vars[6] == 3,
                         block_2_vars[7] == 2, block_2_vars[7] == 3,
                         block_2_vars[8] == 2, block_2_vars[8] == 3
                         )),

        z3.Implies(z3.And(c1 == 12, block_2_vars[10] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1, block_2_vars[9] != 1,
                          ),

                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                         block_2_vars[1] == 2, block_2_vars[1] == 3,
                         block_2_vars[2] == 2, block_2_vars[2] == 3,
                         block_2_vars[3] == 2, block_2_vars[3] == 3,
                         block_2_vars[4] == 2, block_2_vars[4] == 3,
                         block_2_vars[5] == 2, block_2_vars[5] == 3,
                         block_2_vars[6] == 2, block_2_vars[6] == 3,
                         block_2_vars[7] == 2, block_2_vars[7] == 3,
                         block_2_vars[8] == 2, block_2_vars[8] == 3,
                         block_2_vars[9] == 2, block_2_vars[9] == 3,

                         )),

        z3.Implies(z3.And(c1 == 12, block_2_vars[11] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1, block_2_vars[9] != 1,
                          block_2_vars[10] != 1

                          ),

                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                         block_2_vars[1] == 2, block_2_vars[1] == 3,
                         block_2_vars[2] == 2, block_2_vars[2] == 3,
                         block_2_vars[3] == 2, block_2_vars[3] == 3,
                         block_2_vars[4] == 2, block_2_vars[4] == 3,
                         block_2_vars[5] == 2, block_2_vars[5] == 3,
                         block_2_vars[6] == 2, block_2_vars[6] == 3,
                         block_2_vars[7] == 2, block_2_vars[7] == 3,
                         block_2_vars[8] == 2, block_2_vars[8] == 3,
                         block_2_vars[9] == 2, block_2_vars[9] == 3,
                         block_2_vars[10] == 2, block_2_vars[10] == 3,

                         )),

        z3.Implies(z3.And(c1 == 12, block_2_vars[12] == 1,
                          block_2_vars[0] != 1, block_2_vars[1] != 1,
                          block_2_vars[2] != 1, block_2_vars[3] != 1,
                          block_2_vars[4] != 1, block_2_vars[5] != 1,
                          block_2_vars[6] != 1, block_2_vars[7] != 1,
                          block_2_vars[8] != 1, block_2_vars[9] != 1,
                          block_2_vars[10] != 1,  block_2_vars[11] != 1

                          ),

                   z3.Or(block_2_vars[0] == 2, block_2_vars[0] == 3,
                         block_2_vars[1] == 2, block_2_vars[1] == 3,
                         block_2_vars[2] == 2, block_2_vars[2] == 3,
                         block_2_vars[3] == 2, block_2_vars[3] == 3,
                         block_2_vars[4] == 2, block_2_vars[4] == 3,
                         block_2_vars[5] == 2, block_2_vars[5] == 3,
                         block_2_vars[6] == 2, block_2_vars[6] == 3,
                         block_2_vars[7] == 2, block_2_vars[7] == 3,
                         block_2_vars[8] == 2, block_2_vars[8] == 3,
                         block_2_vars[9] == 2, block_2_vars[9] == 3,
                         block_2_vars[10] == 2, block_2_vars[10] == 3,
                         block_2_vars[11] == 2, block_2_vars[11] == 3,
                         )),

    ])


    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)

    assignments = []
    for model in models:

        a = [type_to_str[VariableType(model[ele].as_long())]
             for ele in block_1_vars

             ]

        a.append(type_to_str[ConditionalType(model[c1].as_long())])

        a.extend([type_to_str[VariableType(model[ele].as_long())]
             for ele in block_2_vars

             ])
        a.extend([type_to_str[VariableType(model[ele].as_long())]
                  for ele in block_3_vars

                  ])



        assignments.append(a)
        #print(a)

    #print('Found #{} SAT values'.format(len(models)))
    return assignments


def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:

        ast = ASTNode('run', None, [

               ASTNode(a[0]),
               ASTNode(a[1]),
               ASTNode(a[2]),

               ASTNode(a[3]), ASTNode(a[4]),


               ASTNode('while', a[5], [



                   ASTNode(a[6]), ASTNode(a[7]),
                   ASTNode(a[8]), ASTNode(a[9]),
                   ASTNode(a[10]), ASTNode(a[11]),
                   ASTNode(a[12]), ASTNode(a[13]),
                   ASTNode(a[14]), ASTNode(a[15]),
                   ASTNode(a[16]),
                   ASTNode(a[17]),
                   ASTNode(a[18]),

               ]),

            ASTNode(a[19]), ASTNode(a[20]),
            ASTNode(a[21]),
            ASTNode(a[22]), ASTNode(a[23]),

        ])

        ast = remove_null_nodes(ast)
        all_ast_progs.append(ast)



    return all_ast_progs


def get_p_star():

    Karel_10 = ASTNode('run', None, [
        ASTNode('put_marker'),
        ASTNode('while', 'bool_path_ahead', [
            ASTNode('move'), ASTNode('turn_left'),
            ASTNode('move'), ASTNode('turn_right'), ASTNode('put_marker')
        ])
    ])
    karel_10_json = Karel_10.to_json()
    print("Karel_10:", karel_10_json)

    return Karel_10
