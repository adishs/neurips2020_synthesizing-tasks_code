from z3 import z3


from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block, single_block_change
from utils_ast_smt import ASTNode, remove_null_nodes


def generate_assignments(thresh = 2):

    solver = z3.Solver()
    # declare a block
    block_1 = {'b1_1': 'move', 'b1_2': 'turn_left', 'b1_3': 'move', 'b1_4': 'turn_right'}
    block_1_obj = SMT_Block(block_1, thresh)


    # declare the values that each of the variables can take
    X = [ele.var for ele in block_1_obj.block_z3_vars]


    # declare the values that each of the variables can take
    values = block_1_obj.block_values

    # additional empty block added in the end of the code
    block_2 = {'b2_1': 'phi'}
    block_2_obj = SMT_Block(block_2, thresh)
    values.extend(block_2_obj.block_values)

    # all block objects
    block_objs = [block_1_obj, block_2_obj]

    # declare the values that each of the variables can take
    X.extend([ele.var for ele in block_2_obj.block_z3_vars])

    block_2_vars = [ele.var for ele in block_2_obj.block_z3_vars]



    # declare the constraints on the variables
    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.block_elimination_constraints + \
                  block_2_obj.block_append_constraints + block_2_obj.flip_turns_constraints + block_2_obj.block_elimination_constraints



    single_block_change_cons = single_block_change(block_objs)

    constraints.extend(single_block_change_cons)


    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)
    assignments = []
    for model in models:
        a = [ 'repeat_until_goal (bool_goal)']
        a.extend([type_to_str[VariableType(model[ele].as_long())] for ele in X])
        a.extend([type_to_str[VariableType(model[ele].as_long())] for ele in block_2_vars])
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

               ASTNode(a[1]), ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]),
               ASTNode(a[5]), ASTNode(a[6]), ASTNode(a[7]), ASTNode(a[8]), ASTNode(a[9]), ASTNode(a[10]),
               ASTNode(a[11])
           ])
        ])

        ast = remove_null_nodes(ast)
        all_ast_progs.append(ast)


    return all_ast_progs

def get_p_star():

    HOC_4 = ASTNode('run', None, [ASTNode('repeat_until_goal', 'bool_goal',
                                          [ASTNode('move'), ASTNode('turn_left'),
                                           ASTNode('move'), ASTNode('turn_right')
                                           ])]
                    )
    hoc_4_json = HOC_4.to_json()
    print("HOC_4:", hoc_4_json)

    return HOC_4

