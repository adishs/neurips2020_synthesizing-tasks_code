import json
import sys
import collections
from z3 import z3
import importlib
import os
import time
import pickle
import random

from utils_smt import VariableType, str_to_type, type_to_str,  gen_model, gen_all
from utils_block_smt import SMT_Block
from utils_ast_smt import ASTNode, remove_null_nodes


def generate_mutations_for_taskid(task_id, type,
                                  output_folder, save=False):

    script = 'in_'+str(type)+'_'+str(task_id)

    mod = importlib.import_module(script)

    start_time = time.time()
    assignments = mod.generate_assignments()
    all_ast_progs = mod.generate_ast_nodes_from_assignments(assignments)
    p_star = mod.get_p_star()
    p_star_json = p_star.to_json()
    p_star_size = p_star.size()

    # sort the nodes
    all_ast_progs = list(set(all_ast_progs))  # remove all the repeated programs
    # end_time = time.time()
    all_ast_progs.sort(key=lambda x: x.size())  # sort the programs based on their size

    sizes = []
    if type == "hoc":
        size_tuples = {0: [], 1: [], 2: []}
    elif type == "karel":
        size_tuples = {0: [], 1: [], 2: []}
    else:
        assert "Invalid program type encountered"
        return None

    for ele in all_ast_progs:
        # if ele == p_star:
        #     continue

        sizes.append(ele.size())
        key = ele.size() - p_star_size
        size_tuples[key].append(ele.to_json())


    # shuffle the elements within a size group
    size_keys = list(size_tuples.keys())
    json_progs = []
    for ele in size_keys:
        random.shuffle(size_tuples[ele])
        json_progs.extend(size_tuples[ele])


    # print("Size distribution:", collections.Counter(sizes))
    # print("Number of codes:", len(all_ast_progs))


    if save:
        code_name = 'in-' + str(type) + '-' + str(task_id)

        # create the output directory
        directory = output_folder + code_name + '/'
        if not os.path.exists(directory):
            os.makedirs(directory)

        with open(directory + code_name + '_mutation_info.tsv', 'w') as f:
            f.write("name\tmaxnumblocks\tis_pstar\tgroup_rank\n")
            f.write(code_name + '_mutation-pstar\t'+ str(p_star_size)+'\t'+ str(True) + '\t1\n')

        # save pstar in the file
        fname = directory + code_name + '_mutation-pstar' + '_code.json'
        with open(fname, 'w', encoding='utf-8') as f_code:
            json.dump(p_star_json, f_code, ensure_ascii=False, indent=4)

        with open(directory + code_name + '_mutation_info.tsv', 'a') as f: # append info.tsv to the info file
            for key in size_keys:
                codes = size_tuples[key]
                counter = 1
                for code in codes:
                    name = code_name + '_mutation-' + str(key+p_star_size)+'-'+ str(counter)
                    fname = directory + name + '_code.json'

                    is_pstar = code == p_star_json

                    f.write(name + '\t' + str(key+p_star_size) + '\t' + str(is_pstar)
                            + '\t' + str(counter) + '\n')

                    counter = counter + 1
                    with open(fname, 'w', encoding='utf-8') as f_code:
                        json.dump(code, f_code, ensure_ascii=False, indent=4)

        f.close()

    end_time = time.time()


    return all_ast_progs, json_progs, collections.Counter(sizes), end_time-start_time



def generate_mutations_for_all_tasks(type = 'all', output_folder= '', save= True):

    if type == 'hoc':
            id_list = ['1', '2', '3', '4', '5', '6']

    elif type == 'karel':
            id_list = ['7', '8', '9', '10']

    elif type == 'all':
        all = {}
        all['hoc'] = ['1', '2', '3', '4', '5', '6']
        all['karel'] = ['7', '8', '9', '10']
    else:
        id_list = []
        assert "Incorrect code type"

    all_prog_count = []
    if type == 'hoc' or type == 'karel':
        for ele in id_list:
            ast_list, _, size_dist, exec_time = generate_mutations_for_taskid(ele, type, output_folder, save = save)
            print("Number of programs generated:", len(ast_list))
            all_prog_count.append(["in-"+str(type)+"-"+str(ele),len(ast_list), size_dist, "{:.4f}".format(exec_time)])
    else:
        for key, value in all.items():
            type = key
            id_list = value
            for ele in id_list:
                ast_list, _, size_dist, exec_time = generate_mutations_for_taskid(ele, type, output_folder, save = save)
                print("Number of programs generated:", len(ast_list))
                all_prog_count.append(["in-"+str(type)+"-"+str(ele),len(ast_list), size_dist, "{:.4f}".format(exec_time)])


    #print("All counts:")
    for ele in all_prog_count:
        print(ele)


if __name__ == "__main__":

    output_folder = 'output/'
    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    ### Three modes:
    ### type = 'hoc': Generates mutations only for the HOC tasks
    ### type = 'karel': Generates mutations only for the Karel tasks
    ### type = 'all': Generates mutations for all 10 tasks
    generate_mutations_for_all_tasks(type='all', output_folder= output_folder, save=True)





