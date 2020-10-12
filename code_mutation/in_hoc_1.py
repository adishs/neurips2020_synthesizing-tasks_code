from z3 import z3


from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block
from utils_ast_smt import ASTNode, remove_null_nodes, is_last_child_turn




def generate_assignments(thresh = 2):

    # create the initial z3 solver
    solver = z3.Solver()
    # declare a block
    block_1 = {'b1_1': 'move', 'b1_2': 'turn_left', 'b1_3': 'move', 'b1_4': 'turn_right', 'b1_5': 'move'}
    block_1_obj = SMT_Block(block_1, thresh)

    # declare the values that each of the variables can take
    X =  [ele.var for ele in block_1_obj.block_z3_vars]

    values = block_1_obj.block_values
    constraints = block_1_obj.block_append_constraints + block_1_obj.flip_turns_constraints + block_1_obj.block_elimination_constraints

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
            ASTNode(a[0]), ASTNode(a[1]), ASTNode(a[2]), ASTNode(a[3]), ASTNode(a[4]), ASTNode(a[5]), ASTNode(a[6]),
            ASTNode(a[7]), ASTNode(a[8]), ASTNode(a[9]), ASTNode(a[10]),
            ASTNode(a[11]), ASTNode(a[12])

        ])
        # remove the nodes which are phi'
        ast = remove_null_nodes(ast)

        ##### remove the asts with turn actions in the end
        if not is_last_child_turn(ast):
            all_ast_progs.append(ast)
        ####################################################



    return all_ast_progs


def get_p_star():

    HOC_1 = ASTNode('run', None, [ASTNode('move'), ASTNode('turn_left'),
                                  ASTNode('move'), ASTNode('turn_right'), ASTNode('move')])
    hoc_1_json = HOC_1.to_json()
    print("HOC_1:", hoc_1_json)

    return HOC_1



