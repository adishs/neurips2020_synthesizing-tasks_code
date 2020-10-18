from tqdm import tqdm
from random import shuffle
import numpy as np
import math
import copy

from mcts.get_mcts_binary_tree import get_tree_type, \
        generate_bin_tree, grow_root, grow_type1_loc, grow_type2_loc, grow_type2_while0, \
        grow_type2_while1, grow_type3_loc, grow_type3_while0, grow_type3_while1, \
        grow_type3_if0, grow_type3_if1, grow_type5_loc, grow_type5_if0, \
        grow_type5_if1
from utilities.scoring import compute_score
from mcts.mcts_tree_node import MctsTreeNode

from utilities.karel.environment_karel import EnvironmentKarel
from utilities.karel.dsl_karel import DslKarel
from utilities.karel.program_karel import ProgramKarel

from utilities.utils import WallCrashError, \
        AgentBacktrackingError, AgentOutOfBoundsError, ExecutionTimeoutError, \
        ExceededPreFlippedCoinsError, CoinFlipMismatchError, \
        PickEmptyMarkerError, PutMaxMarkerError

# epsilon value in mcts expression to select a node
EPS = 1e-10

MAX_FUNC_CALLS = 10000


def mcts_binary_trace_to_coin_flips(mcts_trace):
    coin_flips = [ node.val for node in mcts_trace ]

    return coin_flips


def run_mcts_trace_on_env(mcts_trace, input_code, tree_type, env_type, 
            env_type_initial, program):
    task_inputs_str = []
    task_outputs_str = []
    state_sequences = []
    location_traces = []
    hit_infos = []
    locked_cells = []
    agent_input_dirs = []
    agent_input_locs = []
    agent_output_dirs = []
    agent_output_locs = []
    input_markers = []
    locked_wall_cells = []
    symbolic_decisions = []

    l = [node.val for node in mcts_trace]
    #print("mcts trace: ", l)
    coin_flips = mcts_binary_trace_to_coin_flips(mcts_trace)
    #print("coin flips: ", coin_flips)

    if( env_type_initial == "karel" ):
        allow_backtracking = True
    else:
        allow_backtracking = False
    try:
        env = EnvironmentKarel(mode="inverse", coin_flips=coin_flips, world_size=(12, 12), 
                    max_func_calls=MAX_FUNC_CALLS, allow_backtracking=allow_backtracking)
    except WallCrashError:
        # agentloc was populated at a wall cell in the input task constraints
        return [{"crashed" : "WallCrashError"}]

    # add a reference to the env object in the parser object
    program.dsl.parser.env = env
    # flush parser info before run
    program.dsl.parser.flush_hit_info()
    task_input_str = env.draw_array(no_print=True)
    agent_input_dir = env.agent_input_dir
    agent_input_loc = env.agent_input_loc
    # execute program on task
    try:
        env.inverse_run(program)
    except WallCrashError:
        #print ("Exception: agent crashed into wall")
        return [{"crashed" : "WallCrashError"}]
    except AgentBacktrackingError:
        #print ("Exception: agent backtracked to previously visited cell")
        return [{"crashed" : "AgentBacktrackingError"}]
    except ExecutionTimeoutError:
        #print ("Exception: execution exceeded number of allowed symbolic steps")
        return [{"crashed" : "ExecutionTimeoutError"}]
    except PutMaxMarkerError:
        #print("CoinFlipMismatchError")
        return [{"crashed" : "PutMaxMarkerError"}]
    except PickEmptyMarkerError:
        #print("CoinFlipMismatchError")
        return [{"crashed" : "PickEmptyMarkerError"}]
    except AgentOutOfBoundsError:
        #print ("Exception: agent is out of bounds / went outside defined world")
        return [{"crashed" : "AgentOutOfBoundsError"}]
    except ExceededPreFlippedCoinsError:
        #print("ExceededPreFlippedCoinsError")
        return [{"crashed" : "ExceededPreFlippedCoinsError"}]
    except CoinFlipMismatchError:
        #print("CoinFlipMismatchError")
        return [{"crashed" : "CoinFlipMismatchError"}]

    task_output_str = env.draw_array(no_print=True)
    agent_output_dir = env.task.agent.facing
    agent_output_loc = env.task.agent.position
    state_sequence = env.state_sequence
    location_trace = env.location_trace
    # todo union will differ for hoc since no marker cells
    locked_cell = env.locked_empty_cells.union( env.locked_wall_cells.union( env.locked_marker_cells ) ) 
    input_marker = env.input_marker_cells
    locked_wall_cell = env.locked_wall_cells
    hit_info = program.dsl.parser.hit_info
    symbolic_decision = program.dsl.parser.symbolic_decisions
    # remove reference to env object in parser
    program.dsl.parser.env = None

    task_inputs_str.append(task_input_str)
    task_outputs_str.append(task_output_str)
    state_sequences.append(state_sequence)
    location_traces.append(location_trace)
    hit_infos.append(hit_info)
    locked_cells.append(locked_cell)
    agent_input_dirs.append(agent_input_dir)
    agent_input_locs.append(agent_input_loc)
    agent_output_dirs.append(agent_output_dir)
    agent_output_locs.append(agent_output_loc)
    input_markers.append(input_marker)
    locked_wall_cells.append(locked_wall_cell)
    symbolic_decisions.append(symbolic_decision)
    
    return [task_inputs_str, task_outputs_str, state_sequences, location_traces, 
                    hit_infos, locked_cells, agent_input_dirs, agent_input_locs, 
                    agent_output_dirs, agent_output_locs, input_markers, locked_wall_cells, symbolic_decisions]


def score_mcts_trace(mcts_trace, tree_type, input_code, input_task_data, env_type, 
                            env_type_initial, Z, program):
    # run mcts trace on env
    out_list = run_mcts_trace_on_env(mcts_trace, input_code, tree_type, env_type, 
                        env_type_initial, program)
    #print("symbolic_decisions: ", out_list[-1])

    if( len(out_list) == 1 ):
        score_dict = {
            "score_total" : 0.0,
            "crashed": True,
            "crash_type" : out_list[0]["crashed"]
        }
        return score_dict
    
    else:
        trace_info = out_list
        score_dict = compute_score(trace_info, input_task_data, env_type_initial, Z, tree_type, gridsz=12)    
        #k = 0
        #score = ( coverage_score(hit_infos[k]) 
        #               + ( CONST_DISSIM_SCORE *  dissimilarity_score([k], state_sequences, location_traces, input_task_data) )
        #               + ( CONST_QUALITY_SCORE * quality_score([k], state_sequences, location_traces) ) )

        # scale score to lie in [0, 1]
        #score = score / 3.0

        #print("score:", score_dict["score_total"])
        return score_dict


def mcts_tree_node_value(node, expl_const):
    '''
    Expression to select a node in mcts tree traversal is defined here
    '''
    # 1 + node.parent.num_iterations to avoid discontinuity at log(1)
    value = ( 
                node.avg_score + 
                ( expl_const * math.sqrt( math.log(1 + node.parent.num_iterations) / (node.num_iterations + EPS) ) )
            )

    return value


def run_partial_mcts_trace_on_env(mcts_trace, input_code, tree_type, env_type, 
                env_type_initial, program):
    coin_flips = mcts_binary_trace_to_coin_flips(mcts_trace)
    #print(coin_flips)


    if( env_type_initial == "karel" ):
        allow_backtracking = True
    else:
        allow_backtracking = False
    try:
        env = EnvironmentKarel(mode="inverse", coin_flips=coin_flips, world_size=(12, 12), 
                max_func_calls=MAX_FUNC_CALLS, allow_backtracking=allow_backtracking)
    except WallCrashError:
        # agentloc was populated at a wall cell in the input task constraints
        return [{"crashed" : "WallCrashError"}]
    
    # add a reference to the env object in the parser object
    program.dsl.parser.env = env
    # flush parser info before run
    program.dsl.parser.flush_hit_info()
    # execute program on task
    try:
        env.inverse_run(program)
    except CoinFlipMismatchError:
        return False
    except Exception as e:
        return True
    else:
        return True


def isValidNode(node, mcts_trace, input_code, tree_type, env_type, 
                    env_type_initial, program):
    # Check if picking this node (making an mcts decision) is valid 
    # this will remove the CoinFlipMismatchError in the complete mcts_trace
    # This check is performed by executing the partial mcts trace on the environment 
    # and checking for CoinFlipMismatchError

    # todo: usind mcts_trace.append(node) instead of code below modifies mcts_trace in caller filterValidNodes
    # in python: Object references are passed by value
    # understand https://robertheaton.com/2014/02/09/pythons-pass-by-object-reference-as-explained-by-philip-k-dick/
    mcts_trace = mcts_trace + [node]
    
    return run_partial_mcts_trace_on_env(mcts_trace, input_code, tree_type, env_type, 
                        env_type_initial, program)


def filterValidNodes(nodes, mcts_trace, input_code, tree_type, env_type, 
                        env_type_initial, program):
    valid_nodes = []
    for node in nodes:
        #print("mcts_trace in filterValidNodes: ", mcts_trace)
        if( node.valid ):
            valid_nodes.append(node)
        # node.valid is unknown
        elif( node.valid == None ):
            #print("unknown")
            if( isValidNode(node, mcts_trace, input_code, tree_type, env_type, 
                        env_type_initial, program) ):
                valid_nodes.append(node)
                node.valid = True
            else:
                node.valid = False
        # node.valid is False
        else:
            continue

    return valid_nodes


def select_node(nodes, mcts_trace, input_code, tree_type, env_type, env_type_initial, 
                expl_const, program, random=False):
    # filter valid nodes
    #print(len(nodes))
    valid_nodes = filterValidNodes(nodes, mcts_trace, input_code, tree_type, env_type, 
                env_type_initial, program)
    #print(len(valid_nodes))
    if( len(valid_nodes) == 0 ):
        return None

    # in case of a tie, max will return the first maximal item 
    # therefore shuffling nodes to be picked since ties should be broken randomly
    shuffle(valid_nodes)

    if( random ):
        return valid_nodes[0]
    else:
        # nice trick of 2 arguments for 2 function
        # https://stackoverflow.com/questions/22483867/how-to-pass-multiple-arguments-to-the-method-key-of-sorted
        return max(valid_nodes, key=lambda node: mcts_tree_node_value(node, expl_const) )   


def update_node_num_iterations(trace, backprop_idx):
    # if there was no simulation in this rollout
    if( backprop_idx == None ):
        backprop_idx = len(trace) - 1

    for i in range(backprop_idx, -1, -1):
        trace[i].num_iterations += 1    


def update_node_scores(trace, score, backprop_idx):
    # if there was no simulation in this rollout
    if( backprop_idx == None ):
        backprop_idx = len(trace) - 1

    for i in range(backprop_idx, -1, -1):
        # update average score of node
        n_i = trace[i].num_iterations
        avg_score = trace[i].avg_score
        trace[i].avg_score = ((n_i * avg_score) + score) / (n_i + 1) 


def expand_node(node, cnt_node_expansions, expanded_nodes):
    if( node.compressed ):
        node.compressed = False
        node.avg_score = 0
        node.num_iterations = 0
        node.num_picked = 0
        node.valid = None
        node.score_dict = {}
        node.is_minimal_delta_debug = None
        node.is_minimal_shortest_path = None
        cnt_node_expansions[0] += 1
        expanded_nodes.append(node)
    else:
        pass


def reset_node(node):
    # by setting compressed=True, the node will be automatically reset when expanded by expand_node in next mcts run
    node.compressed = True


def grow_node(node, tree_type, cnt_node_grown, depth):
    grow_fn = {
        "type-1" : {
            "max_depth" : 1,
            "root" : grow_root,
            "loc" : grow_type1_loc
        },
        "type-2" : {
            "max_depth" : depth + 1,
            "root" : grow_root,
            "loc" : grow_type2_loc,
            "while0" : grow_type2_while0,
            "while1" : grow_type2_while1
        },
        "type-3" : {
            "max_depth" : (depth*2) + 1,
            "root" : grow_root,
            "loc" : grow_type3_loc,
            "while0" : grow_type3_while0,
            "while1" : grow_type3_while1,
            "if0" : grow_type3_if0,
            "if1" : grow_type3_if1
        },
        "type-5" : {
            "max_depth" : depth + 1,
            "root" : grow_root,
            "loc" : grow_type5_loc,
            "if0" : grow_type5_if0,
            "if1" : grow_type5_if1
        }
    }

    if( not node.grown ):
        # grow node
        grow_fn[tree_type][node.node_type](node, grow_fn[tree_type]["max_depth"])
        node.grown = True
        cnt_node_grown[0] += 1
    else:
        pass  


def train_mcts_tree(tree_type, num_train_iterations, input_code, input_task_data, env_type, 
                    env_type_initial, Z, expl_const, program, depth):
    # create root node of mcts tree
    root = MctsTreeNode( node_type="root", parent=None, children=[], val="root", depth=0 )
    # snapshot_t stores at which t to take a snapshot of the mcts tree
    #snapshot_t = [16, 32, 64, 128, 1000, 2500, 5000, 7500, 10000]
    #snapshot_roots = {}

    flag_no_valid_children = False
    # no of times scores were reused from cached score table
    score_table_hits = 0
    unique_traces = []
    all_traces = []
    cnt_invalid_traces = 0
    cnt_node_expansions = [0]
    cnt_node_grown = [0]
    t = 1
    # store a list of expanded nodes to be reset for diversity
    #expanded_nodes = []
    #grown_nodes = []

    # expand root node once for all t training iterations
    #expand_node(root, cnt_node_expansions, expanded_nodes)
    grow_node(root, tree_type, cnt_node_grown, depth)

    # initialize tqdm progress bar
    pbar = tqdm(total=num_train_iterations+1)

    # for each training iteration do
    while( t<=num_train_iterations ):
        # increment num_iterations of root
        # needed since parent's node num_iterations is used in node selection
        root.num_iterations += 1
        
        # initialize
        curr_node = root
        mcts_trace = []
        # index in trace to start backpropogation update from (inclusive)
        # this index is the node from which simulation begins in mcts terminology 
        backprop_idx = None
        
        # selection - compute a mcts trace from root to a leaf
        while(curr_node.children != []):
            # before selection check each child node is in expanded state
            #for child in curr_node.children:
            #    expand_node(child, cnt_node_expansions, expanded_nodes)

            # simulation stage
            if( backprop_idx != None ):
                # select node at random
                selected_node = select_node(curr_node.children, mcts_trace, input_code, tree_type, 
                            env_type, env_type_initial, expl_const, program, random=True)
                if( selected_node == None ):
                    curr_node.valid = False
                    flag_no_valid_children = True
                    break
            else:
                # selection stage
                selected_node = select_node(curr_node.children, mcts_trace, input_code, tree_type, 
                            env_type, env_type_initial, expl_const, program)
                if( selected_node == None ):
                    curr_node.valid = False
                    flag_no_valid_children = True
                    break
                # expansion to include the first num_iterations=0 node
                if( (selected_node.num_iterations == 0) and (backprop_idx == None) ):
                    # since backprop_idx is the len it will include the new node to be updated added to mcts_trace later
                    backprop_idx = len(mcts_trace)
            mcts_trace.append(selected_node)
            curr_node = selected_node

            # grow curr_node for next selection / simulation step
            grow_node(curr_node, tree_type, cnt_node_grown, depth)

        if( flag_no_valid_children ):
            flag_no_valid_children = False
            cnt_invalid_traces += 1
            # continue without increment mcts iteration counter t
            continue

        else:
            # compute score of mcts trace
            # reuse cached leaf scores if previously visited
            if( mcts_trace[-1].num_picked == 0 ):
                score_dict = score_mcts_trace(mcts_trace, tree_type, input_code, input_task_data, 
                                    env_type, env_type_initial, Z, program)
                mcts_trace[-1].score_dict = score_dict
                unique_traces.append(mcts_trace)
                score = score_dict["score_total"]
                #all_traces.append(mcts_trace)
            else:
                score_table_hits += 1
                score = mcts_trace[-1].score_dict["score_total"]
                #all_traces.append(mcts_trace)

            mcts_trace[-1].num_picked += 1
            
            # backpropagation 
            # update average scores of selected nodes
            update_node_scores(mcts_trace, score, backprop_idx)
            # update iteration counts of selected nodes
            update_node_num_iterations(mcts_trace, backprop_idx)

            # take snapshots of evolving tree at different t 
            #if( t+1 in snapshot_t ):
            #   snapshot_roots[t] = copy.deepcopy(root)

            # increment mcts iteration counter t
            t += 1
            # update tqdm progress bar
            pbar.update(1)

    # close tqdm progress bar
    pbar.close()

    # remove individual variables above, access keys in dictionary directly
    mcts_info = { "mcts_run_totaliters" : num_train_iterations,
                "mcts_run_num_unique_traces" : len(unique_traces),
                "mcts_run_num_repeat_traces" : score_table_hits,
                "mcts_run_num_invalid_traces" : cnt_invalid_traces
    }

    #return root, score_table_hits, unique_traces, mcts_info, cnt_node_expansions, expanded_nodes, all_traces
    return score_table_hits, unique_traces, mcts_info, cnt_node_grown, all_traces

