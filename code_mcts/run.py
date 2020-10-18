import argparse
from pathlib import Path
import time
import os
import json
import random
import string
import subprocess

from utilities.ast_to_code_converter import convert_ast_to_code
from utilities.utils_shortest_path_on_grid import prune_using_shortest_path_hoc
from mcts.mcts_algorithm import train_mcts_tree, run_mcts_trace_on_env, mcts_binary_trace_to_coin_flips, reset_node
from mcts.get_mcts_binary_tree import get_tree_type
from utilities.karel.dsl_karel import DslKarel
from utilities.karel.program_karel import ProgramKarel


MCTS_TREE_DEPTH = 20
MCTS_NUM_TRAIN_ITERATIONS = 2000000
MCTS_EXPLORATION_CONST = 2

map_paper_task_id_to_code_task_id ={
    "H1" : "in-hoc-A", 
    "H2" : "in-hoc-C", 
    "H3" : "in-hoc-D", 
    "H4" : "in-hoc-F", 
    "H5" : "in-hoc-G", 
    "H6" : "in-hoc-H",
    
    "K7" : "in-karel-A", 
    "K8" : "in-karel-C", 
    "K9" : "in-karel-E", 
    "K10" : "in-karel-F"
}
quality_score_thresholds = {
    "in-hoc-A" : 0,
    "in-hoc-C" : 0,
    "in-hoc-D" : 0,
    "in-hoc-F" : 0.2,
    "in-hoc-G" : 0.2,
    "in-hoc-H" : 0.2,
    
    "in-karel-A" : 0,
    "in-karel-C" : 0,
    "in-karel-E" : 0,
    "in-karel-F" : 0.2
}
dir_name_to_tuple = {
    'east': (1, 0),
    'north': (0, -1),
    'west': (-1, 0),
    'south': (0, 1),
}
task_info = { 
    "in-hoc-A" : {
        "pstar_num_blocks" : 5
    },
    "in-hoc-C" : {
        "pstar_num_blocks" : 3
    },
    "in-hoc-D" : {
        "pstar_num_blocks" : 5
    },
    "in-hoc-F" : {
        "pstar_num_blocks" : 5
    },
    "in-hoc-G" : {
        "pstar_num_blocks" : 4
    },
    "in-hoc-H" : {
        "pstar_num_blocks" : 4
    }, 

    "in-karel-A" : {
        "pstar_num_blocks" : 5
    },
    "in-karel-C" : {
        "pstar_num_blocks" : 4
    },
    "in-karel-E" : {
        "pstar_num_blocks" : 5
    },
    "in-karel-F" : {
        "pstar_num_blocks" : 7
    }
}
EPSILON = 1e-6


def main():
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument('--data_out_path', type=str, default="./output/", help='output folder path for new tasks')
    arg_parser.add_argument('--input_task_id', type=str, required=True, help='task_id in correct format: in-hoc-A / in-karel-E / etc')
    arg_parser.add_argument('--input_program_path', type=str, required=True, help='path to program as AST in json format')
    arg_parser.add_argument('--num_diverse_tasks', type=int, default=10, help='number of diverse new tasks to generate for input task')
    args = arg_parser.parse_args()

    # create folder for storing new tasks
    #tasks_folder = os.path.join(args.data_out_path, "tasks")
    #Path(tasks_folder).mkdir(parents=True, exist_ok=True)

    task_path = os.path.join("./input/", "{}_task-in.txt".format(args.input_task_id))
    with open(task_path) as f:
        input_task = f.read()
    # convert AST json file to code sequence
    with open(args.input_program_path) as f:
        input_ast = json.load(f)
    input_code = convert_ast_to_code(input_ast)

    # get environment type HOC / Karel
    if( "hoc" in input_task ):
        env_type = "hoc"
    else:
        env_type = "karel" 
    # HOC / Karel programs are executed as Karel programs
    env_type_execution = "karel"

    # create temp folder for pruning
    #temp_folder = "./output/temp"
    #Path(temp_folder).mkdir(parents=True, exist_ok=True)

    # map task id notation in paper to older task id notation used in code internally
    input_task_id = map_paper_task_id_to_code_task_id[args.input_task_id]
    
    # get mcts tree type
    tree_type = get_tree_type(input_task_id[3:])

    # depth of tree type 5 is parameterized by repeat counter in code
    if( tree_type == "type-5" ):
        global MCTS_TREE_DEPTH
        for block in input_ast["children"]:
            if( "repeat" in block["type"] ):
                MCTS_TREE_DEPTH = int(block["type"].split("(")[1][:-1])
        assert (MCTS_TREE_DEPTH >=2 and MCTS_TREE_DEPTH <= 10), "r in tree type 5 not in [2,9]"

    # get input task data
    if( env_type == "karel" ):
        with open(task_path) as f:
            lines = f.readlines()
        # pregrid
        pregrid = lines[4:16]
        pregrid = ["".join(line.strip().split("\t")[1:]) for line in pregrid]
        # postgrid
        postgrid = lines[20:32]
        postgrid = ["".join(line.strip().split("\t")[1:]) for line in postgrid]
        # agentloc 
        pos = lines[16].strip().split("\t")[1]
        x = int(pos.split(",")[0][1:]) - 1
        y = int(pos.split(",")[1][:-1]) - 1
        agent_input_loc = (x+1, y+1)
        # agentdir
        dir_name = lines[17].strip().split("\t")[1]
        agent_input_dir = dir_name_to_tuple[dir_name]
        
        input_task_data = {"agent_input_loc" : agent_input_loc,
                            "agent_input_dir" : agent_input_dir,
                            "pregrid" : pregrid,
                            "postgrid" : postgrid,
                            "input_gridsz" : 12
                            }
    else:
        # todo : can make the parsing extremely file format specific allowing faster reading like karel above
        with open(task_path) as f:
            read_flag = False
            lines = []
            for line in f.readlines():
                if("pregrid" in line):
                    read_flag = True
                    continue
                if( read_flag == True ):
                    if( "agentloc" in line ):
                        pos = line.strip().split("\t")[1]
                        x = int(pos.split(",")[0][1:]) - 1
                        y = int(pos.split(",")[1][:-1]) - 1
                        # todo check location indexing
                        agent_input_loc = (x+1, y+1)
                    elif( "agentdir" in line ):
                        dir_name = line.strip().split("\t")[1]
                        agent_input_dir = dir_name_to_tuple[dir_name]
                    else:   
                        line = "".join(line.strip().split("\t")[1:])
                        lines.append(line)
        
        input_task_data = {"agent_input_loc" : agent_input_loc,
                            "agent_input_dir" : agent_input_dir,
                            "pregrid" : lines,
                            # input task gridsz is always 12 for now
                            "input_gridsz" : 12
                            }

    # set Z stores the set of new tasks picked
    Z = []
    task_cnt = 0
    for i in range(args.num_diverse_tasks):
        print("getting diverse task: ", i+1)

        # train mcts tree
        start_time_train_mcts_tree = time.time()
        # get dsl and program object at the beginning to share across mcts iterations
        if( env_type == "karel" ):
            allow_backtracking = True
        else:
            allow_backtracking = False
        dsl = DslKarel()    
        program = ProgramKarel(input_code, dsl)
        score_table_hits, unique_traces, mcts_info, cnt_node_grown, all_traces = train_mcts_tree( 
                                tree_type, MCTS_NUM_TRAIN_ITERATIONS, input_code, input_task_data, 
                                env_type_execution, env_type, Z, MCTS_EXPLORATION_CONST, program, 
                                MCTS_TREE_DEPTH)
        end_time_train_mcts_tree = time.time()
        mcts_tree_train_time = round(end_time_train_mcts_tree - start_time_train_mcts_tree, 2)
        print("time taken to train mcts tree: ", mcts_tree_train_time)

        # pick top trace from pool of mcts traces seen during training after pruning
        start_time_pick_trace = time.time()
        max_mcts_trace = pick_top_trace_with_pruning(unique_traces, args.input_program_path, args.data_out_path, 
                                    env_type, input_code, tree_type, env_type_execution, input_task_id, 
                                    task_info[input_task_id]["pstar_num_blocks"], program)
        end_time_pick_trace = time.time()
        mcts_tree_pick_trace_time = round(end_time_pick_trace - start_time_pick_trace, 2)
        print("time taken to pick trace: ", mcts_tree_pick_trace_time)

        # finish post processing of current run
        if( max_mcts_trace == None ):
            print("no new task found")
            break
        else:
            # write trace info as new task file
            out_list = run_mcts_trace_on_env(max_mcts_trace, input_code, tree_type, 
                    env_type_execution, env_type, program)
            (task_inputs_str, task_outputs_str, state_sequences, location_traces, hit_infos, 
                    locked_cells, agent_input_dirs, agent_input_locs, agent_output_dirs, agent_output_locs, 
                    input_markers, locked_wall_cells, symbolic_decisions) = out_list  

            # save new task to file     
            fname_prefix = args.input_task_id + "_diverse-{}".format(i+1)   
            write_input_output_pair(task_inputs_str[0], task_outputs_str[0], 
                        state_sequences[0], location_traces[0], locked_cells[0],
                        agent_input_dirs[0], agent_input_locs[0], agent_output_dirs[0],
                        agent_output_locs[0], input_markers[0], locked_wall_cells[0],
                        fname_prefix, args.data_out_path, env_type, 0, args.input_program_path)

            # update set of picked traces
            Z.append(out_list)
            task_cnt += 1


def pick_top_trace_with_pruning(unique_traces, code_path, data_out_path, env_type, 
                    input_code, tree_type, env_type_execution, task_id, maxnumblocks, program):
    # todo make this more optimal - don't read write to file, etc
    unique_traces.sort(key=lambda trace: trace[-1].score_dict["score_total"], reverse=True)
    # since the temp folder is shared, to prevent parallel process to access the same file, adding a random string
    random_str = ''.join(random.choices(string.ascii_uppercase + string.digits, k=64))
    for trace in unique_traces:
        # if crashed
        if( "crashed" in trace[-1].score_dict ):
            continue
        # if coverage != 1
        elif( trace[-1].score_dict["score_coverage"] != 1 ):
            continue
        # quality score based pruning
        elif( trace[-1].score_dict["score_quality"] < quality_score_thresholds[task_id] ):
            continue
        # filter invalid traces marked with 0.0 total_score (repeat traces in diversity and repeating input trace)
        elif( trace[-1].score_dict["score_total"] < EPSILON ):
            continue
        # else prune using graph shortest path and check minimal
        else:
            # write temp task file for trace
            if( env_type == "hoc" ):
                filename_prefix = "temp_hoc_" + random_str
                out_filename = "temp_hoc_{}_task.txt".format(random_str)
            else:
                filename_prefix = "temp_karel_" + random_str
                out_filename = "temp_karel_{}_task.txt".format(random_str) 
            out_list = run_mcts_trace_on_env( trace, input_code, tree_type, env_type_execution, 
                            env_type, program)
            (task_inputs_str, task_outputs_str, state_sequences, location_traces, 
                        hit_infos, locked_cells, agent_input_dirs, agent_input_locs, agent_output_dirs, 
                        agent_output_locs, input_markers, locked_wall_cells, symbolic_decisions) = out_list
            write_input_output_pair(task_inputs_str[0], task_outputs_str[0], 
                        state_sequences[0], location_traces[0], locked_cells[0],
                        agent_input_dirs[0], agent_input_locs[0], agent_output_dirs[0],
                        agent_output_locs[0], input_markers[0], locked_wall_cells[0],
                        filename_prefix, data_out_path, env_type, 1, code_path)
            task_path = os.path.join("./output/temp", out_filename)

            # prune_using_shortest_path_hoc - true if p_in code with maxnumblocks is minimal code, 
            # false if shorter or equal length code is found
            # disable path pruning for karel
            if( env_type != "karel" ):
                # only prune strictly shorter code for hoc-A
                if( task_id == "in-hoc-A" ):
                    if( prune_using_shortest_path_hoc(task_path, maxnumblocks) == "lesser" ):
                        trace[-1].is_minimal_shortest_path = False
                        continue
                # for other task-ids prune shorter and equal to code
                else:
                    result = prune_using_shortest_path_hoc(task_path, maxnumblocks)
                    if(( result == "lesser" ) or ( result == "equal" )):
                        trace[-1].is_minimal_shortest_path = False
                        continue
            trace[-1].is_minimal_shortest_path = True
            return trace

    return None


def get_direction_string(direction):
    if( direction == (-1, 0) ):
        return "west"
    elif( direction == (1, 0) ):
        return "east"
    elif( direction == (0, -1) ):
        return "north"
    else:
        return "south"


def write_input_output_pair(task_input_str, task_output_str, 
                        state_sequence, location_trace, locked_cell,
                        agent_input_dir, agent_input_loc, agent_output_dir,
                        agent_output_loc, input_marker, locked_wall_cell,
                        filename_prefix, directory, env_type, temp, 
                        program_path):
    gridsz = 12
    if( temp == 1 ):
        out_filename = filename_prefix + "_task.txt"
        filename = os.path.join("./output/temp", out_filename) 
    elif( temp == 3 ):
        out_filename = filename_prefix + "_task.txt"
        filename = os.path.join(directory, out_filename)
    else:
        # copy code file - using cp from linux is fastest (assumption) over python copying
        #directory = os.path.join(directory, "tasks")
        #program_out_path = os.path.join(directory, filename_prefix + "_code.json")
        #subprocess.call("cp {} {}".format(program_path, program_out_path), shell=True)

        out_filename = filename_prefix + "_task-out.txt"
        filename = os.path.join(directory, out_filename)

    if( env_type == "hoc" ):
        # fill surrounding of output grid with wall cells
        all_cells = set()
        for i in range(gridsz):
            for j in range(gridsz):
                all_cells.add(str(i) + '#' + str(j))
        surrounding_wall_cells = all_cells.difference(locked_cell)
        for pos in surrounding_wall_cells:
            i = int(pos.split("#")[0])
            j = int(pos.split("#")[1])
            task_output_str[i][j] = "#"     

        # add goal to output grid (since some tasks don't have a while(no goal))
        x = agent_output_loc[0] 
        y = agent_output_loc[1]
        task_output_str[y][x] = "+"

        # start writing to file
        write_string = ""
        with open(filename, "w") as f:      
            write_string += "type\thoc\n"
            write_string += "gridsz\t" + "(" + str(gridsz) + "," + str(gridsz) + ")" + "\n"
            write_string += "\n"
            write_string += "pregrid"
            for i in range(1, gridsz+1):
                write_string += "\t" + str(i)
            write_string += "\n"

            task_output_str = ["\t".join(row.tolist()) for row in task_output_str]
            for i in range(1, len(task_output_str)+1):
                write_string += str(i) + "\t"
                write_string += task_output_str[i-1]
                write_string += "\n"

            x = agent_input_loc[0] + 1
            y = agent_input_loc[1] + 1
            write_string += "agentloc\t" + "(" + str(x) + "," + str(y) + ")" + "\n"

            agent_input_dir = get_direction_string(agent_input_dir)
            write_string += "agentdir\t" + agent_input_dir + "\n"

            f.write(write_string)

    else:
        # place input markers in input grid
        for pos in input_marker:
            i = int(pos.split("#")[0])
            j = int(pos.split("#")[1])
            task_input_str[i][j] = "x"
        # place walls in input grid
        for pos in locked_wall_cell:
            i = int(pos.split("#")[0])
            j = int(pos.split("#")[1])
            task_input_str[i][j] = "#"
        
        # start writing to file
        write_string = ""
        with open(filename, "w") as f:      
            write_string += "type\tkarel\n"
            write_string += "gridsz\t" + "(" + str(gridsz) + "," + str(gridsz) + ")" + "\n"
            write_string += "\n"

            # write pregrid
            write_string += "pregrid\t"
            for i in range(1, gridsz+1):
                write_string += str(i) + "\t"
            write_string += "\n"

            task_input_str = ["\t".join(row.tolist()) for row in task_input_str]
            for i in range(1, len(task_input_str)+1):
                write_string += str(i) + "\t"
                write_string += task_input_str[i-1]
                write_string += "\n"

            x = agent_input_loc[0] + 1
            y = agent_input_loc[1] + 1
            write_string += "agentloc\t" + "(" + str(x) + "," + str(y) + ")" + "\n"

            agent_input_dir = get_direction_string(agent_input_dir)
            write_string += "agentdir\t" + agent_input_dir + "\n"   
            write_string += "\n"

            # write postgrid    
            write_string += "postgrid\t"
            for i in range(1, gridsz+1):
                write_string += str(i) + "\t"
            write_string += "\n"

            task_output_str = ["\t".join(row.tolist()) for row in task_output_str]
            for i in range(1, len(task_output_str)+1):
                write_string += str(i) + "\t"
                write_string += task_output_str[i-1]
                write_string += "\n"

            x = agent_output_loc[0] + 1
            y = agent_output_loc[1] + 1
            write_string += "agentloc\t" + "(" + str(x) + "," + str(y) + ")" + "\n"

            agent_output_dir = get_direction_string(agent_output_dir)
            write_string += "agentdir\t" + agent_output_dir + "\n"

            f.write(write_string)


if __name__ == '__main__':
    main()

