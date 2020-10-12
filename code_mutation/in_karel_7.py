from z3 import z3


from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block
from utils_ast_smt import ASTNode, remove_null_nodes


def generate_assignments(thresh = 2, id = 'karel'):

    # create the initial z3 solver
    solver = z3.Solver()
    # declare a block
    block_1 = {'b1_1': 'move', 'b1_2': 'move', 'b1_3': 'pick_marker', 'b1_4': 'move', 'b1_5': 'move'}
    block_1_obj = SMT_Block(block_1, thresh, id =id )

    # declare the values that each of the variables can take
    X =  [ele.var for ele in block_1_obj.block_z3_vars]

    values = block_1_obj.block_values
    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + \
                  block_1_obj.flip_marker_constraints + block_1_obj.block_elimination_constraints

    # add the values and the constraints
    solver.add(values + constraints)

    # generate all the assignments
    models = gen_all(solver, X)
    assignments = []
    for model in models:
        a = [type_to_str[VariableType(model[ele.var].as_long())]
            for ele in block_1_obj.block_z3_vars
             ]

        assignments.append(a)
        #print(a)



    #print('Found #{} SAT values'.format(len(models)))
    return assignments


def generate_ast_nodes_from_assignments(assignments: list):

    all_ast_progs = []

    for a in assignments:
        ast = ASTNode('run', None, [
            ASTNode(a[0]), ASTNode(a[1]),
            ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]), ASTNode(a[5]),
            ASTNode(a[6]), ASTNode(a[7]), ASTNode(a[8]), ASTNode(a[9]), ASTNode(a[10]),
            ASTNode(a[11]), ASTNode(a[12]),

        ])
        # remove the nodes which are phi
        ast = remove_null_nodes(ast)
        all_ast_progs.append(ast)


    return all_ast_progs

def get_p_star():

    Karel_7 = ASTNode('run', None, [ASTNode('move'), ASTNode('move'),
                                    ASTNode('pick_marker'), ASTNode('move'), ASTNode('move')])

    karel_7_json = Karel_7.to_json()
    print("Karel_7:", karel_7_json)

    return Karel_7


