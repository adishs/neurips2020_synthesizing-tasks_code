This folder contains code files related to our paper titled "Synthesizing Tasks for Block-based Programming".
In particular, the code files correspond to the 'Mutation-Stage' of our proposed pipeline. 
We generate code mutations for 10 reference tasks from the HOC/Karel platforms.

We describe the code files next.

### mutations.py
Run Command: python mutation.py

This is the main file which when run generates the mutated codes for all 10 reference tasks, in the folder 'output/'

#### Output of mutations.py
All the mutated codes are generated in the 'output/' folder, and mutations of the reference codes are stored in folders named after their corresponding Code-IDs.
Additionally, the total count of the all mutated codes generated, their distribution based on code-size, along with their runtimes is displayed. 
Each code mutation output folder contains the reference code file with the extension '-pstar_code.json', and an information file with the extension, '_info.tsv', which lists the name(field:name), size of each generated mutated code (field: maxnumblocks), whether it is the same as the reference code (field: is_pstar), and the group rank of the mutated code(field: group_rank). 
The group rank gives the ID of the mutated code file in their respective size (code size) group. 
The mutated code files are named as follows:
$code-id\_mutation-$size-$group_rank\_code.json

### utils_*.py

We have 3 'utils' files which contain common routines shared by all 10 reference tasks. These 'utils' are:
1. utils_ast_smt.py - This file contains routines/classes that generate the AST structure from raw text code files, and have operations defined on them.
2. utils_block_smt.py - This file contains routines/classes that generate all the SMT-constraints for any 'action-sequence' in the sketch of the code.
3. utils_smt.py - This file contains functions that define an SMT-model from the constraints supplied, and generates the assignments for the specific SMT-query.

### in_hoc_\*.py/ in_karel_\*.py

Each of these code files, contain all the constraints corresponding to their reference code. The basic structure of these files is as follows:
1. generate_assignments(thresh = 2) - This routine defines all the constraints for the reference code, with \delta_size (thresh)=2,calls the SMT-solver to generate all valid assignments.
2. generate_ast_nodes_from_assignments(assignments: list) - This routine generates AST structure of the code from the SMT-assignments. Empty nodes (\phi) are pruned out.
3. get_p_star() - This routine returns the reference code for the corresponding task-ID.