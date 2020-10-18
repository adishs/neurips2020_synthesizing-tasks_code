# [Synthesizing Tasks for Block-based Programming](https://arxiv.org/abs/2006.16913)
Given a reference visual task T<sup>in</sup> and its solution code C<sup>in</sup>, our task synthesis algorithm first mutates C<sup>in</sup> to obtain a set of codes {C<sup>out</sup>}. Then, our algorithm performs symbolic execution over a code C<sup>out</sup> to obtain a new visual task T<sup>out</sup>. `neurips20_mcts` contains code for the symbolic execution stage of our algorithm, it takes T<sup>in</sup> and C<sup>out</sup> as input, and generates (multiple diverse) T<sup>out</sup>.

## Requirements

| Item       | Version       | 
| ------------- |:-------------:| 
| python     | 3.7.5 |
| decorator     | 4.4.2 |
| networkx      | 2.5      |  
| numpy | 1.19.2      |   
| pandas | 1.1.3      |   
| ply | 3.11      |   
| pyparsing | 2.4.7      | 
| python-dateutil | 2.8.1      | 
| pytz | 2020.1      | 
| scipy | 1.5.2      | 
| six | 1.15.0      | 
| tqdm | 4.50.2      | 


## Usage

To reproduce Fig. 1 in our paper, run:

`python run.py --input_task_id=H5 --input_program_path=./input/H5_code-out.json --num_diverse_tasks=1`

To reproduce Fig. 2 in our paper, run:

`python run.py --input_task_id=K10 --input_program_path=./input/K10_code-out.json --num_diverse_tasks=1`

where:
* input_task_id is the input task T<sup>in</sup>, (required)
* input_program_path is the path to program C<sup>out</sup> for corresponding T<sup>in</sup>, (required)
* num_diverse_tasks is the number of diverse new tasks T<sup>out</sup> to generate for T<sup>in</sup>, (optional, default=10)

Note: The generated new task T<sup>out</sup> may not always be exactly the same as shown in our paper.

## Code Organization

## Citation

