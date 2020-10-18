'''
code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

import numpy as np
from collections import Counter

from utilities.utils import get_rng, WallCrashError, \
            AgentBacktrackingError, AgentOutOfBoundsError, ExecutionTimeoutError, \
            ExceededPreFlippedCoinsError, CoinFlipMismatchError


def border_mask(array, value):
    array[0,:], array[-1,:], array[:,0], array[:,-1] = value, value, value, value


# define decorator function
# todo understand *args, **kwargs
# todo understand the purpose of agent_action decorator
def agent_action(func):
    def fn(*args, **kwargs):
        self = args[0]
        out = func(self)
        if self.debug:
            print(func.__doc__, out)
            # todo should we implement draw for viz, or is ascii viz enough,
            # or is curses lib viz used in https://github.com/alts/karel better?
            #self.draw()
        return out
    return fn


# define decorator function
def world_condition(func):
    def fn(*args, **kwargs):
        self = args[0]
        out = func(self)
        if self.debug:
            print(func.__doc__, out)
        return out
    return fn


class Environment(object):
    # class attributes
    AGENT_CHARS = "<^>v"
    WALL_CHAR = '#'
    EMPTY_CHAR = '.'
    UNKNOWN_CHAR = '?'

    def __init__( 
            self, rng=None, debug=False, max_func_calls=10000 ):

        self.debug = debug
        #self.rng = get_rng(rng)
        self.agent_direction = 4
        self.num_func_calls = 0
        self.max_func_calls = max_func_calls
        self.state_sequence = []
        self.location_trace = []


    # todo is virtual method the best way to define code for random_world, parse_world and parse_state?
    # virtual method - not really required since python methods are always virtual
    # https://stackoverflow.com/questions/4714136/how-to-implement-virtual-methods-in-python
    def random_world(self, world_size, wall_ratio):
        # this method should be overrided in derived classes
        raise NotImplementedError()


    # virtual method
    # todo : when implementing this method in derived classes need to check for more kinds of errors
    # like no agent, more than one agent, etc
    def parse_world(self, world_path):
        # this method should be overrided in derived classes
        raise NotImplementedError()


    # virtual method
    def parse_state(self, state):
        # this method should be overrided in derived classes
        raise NotImplementedError()


    # todo check logic is correct
    def agent_char(self):
        # index will be in (-2, -1, 1, 2)
        index = self.task.agent.facing[0] + 2*self.task.agent.facing[1]
        return ' >v^<'[index]


    # defining agent actions in environment
    @agent_action
    def move(self):
        '''Move'''
        success = True
        
        if (not self._front_is_clear_for_move()):
            curr_loc = str(self.task.agent.position[1]) + '#' + str(self.task.agent.position[0])
            #print(curr_loc)
            #print(self.task.agent.facing)
            raise WallCrashError
            success = False
        else:
            self.task.agent.move()

            if( self.mode == "inverse" ):
                curr_loc = str(self.task.agent.position[1]) + '#' + str(self.task.agent.position[0])
                # todo : below commented line to not needed right since cell is already added in locked list?
                self.locked_empty_cells.add(curr_loc)
                # todo : allow backtracking in Karel
                if ( (curr_loc in self.location_trace) and (self.allow_backtracking == False) ):
                    raise AgentBacktrackingError
                    #self.state_sequence.append("error: backtrack")
                self.location_trace.append(curr_loc)
                self.state_sequence.append("move")
            else:
                curr_loc = str(self.task.agent.position[1]) + '#' + str(self.task.agent.position[0])
                self.location_trace.append(curr_loc)
                self.state_sequence.append("move")            
        
        return success


    @agent_action
    def turn_left(self):
        '''Turn left'''
        curr_loc = str(self.task.agent.position[1]) + '#' + str(self.task.agent.position[0])
        self.location_trace.append(curr_loc)
        self.task.agent.turn_left()
        self.state_sequence.append("turn_left")


    @agent_action
    def turn_right(self):
        '''Turn right'''
        curr_loc = str(self.task.agent.position[1]) + '#' + str(self.task.agent.position[0])
        self.location_trace.append(curr_loc)
        self.task.agent.turn_right()
        self.state_sequence.append("turn_right")


    # defining world condition checks in environment
    @world_condition
    def front_is_clear(self):
        '''Check front is clear'''
        return self._front_is_clear()


    def _front_is_clear(self):
        next_x = self.task.agent.position[0] + self.task.agent.facing[0]
        next_y = self.task.agent.position[1] + self.task.agent.facing[1]
        new_loc = str(next_y) + "#" + str(next_x)

        if( not self.record_func_call() ):
            raise ExecutionTimeoutError
        # max x in 2D real world corresponds to max column index = width of world
        elif( (next_x >= self.width) or (next_y >= self.height) ):
            raise AgentOutOfBoundsError
        else:
            if( self.mode == "inverse" ):
                # get a coin flip
                if( self.coin_flips != None ):
                    if( self.coin_flip_idx < len(self.coin_flips) ):
                        coin_toss = self.coin_flips[self.coin_flip_idx]
                        self.coin_flip_idx += 1
                    else:
                        # this exception should logically never be thrown
                        raise ExceededPreFlippedCoinsError                        
                else:
                    coin_toss = np.random.choice([0, 1], p=[1-self.prob_front_is_clear, self.prob_front_is_clear])

                if( new_loc not in ( self.locked_empty_cells | self.locked_wall_cells | self.locked_marker_cells ) ):
                    if( coin_toss ):
                        self.locked_empty_cells.add(new_loc)
                        self.state_sequence.append("front_is_clear=true")
                        self.task.world[next_y][next_x] = '.'
                    else:
                        self.locked_wall_cells.add(new_loc)
                        self.state_sequence.append("front_is_clear=false")
                        self.task.world[next_y][next_x] = '#'
                
                else:
                    # check if in mcts inverse mode
                    if( self.coin_flips != None ):
                        # check for coin flip mismatch
                        # mcts intended coin toss doesn't match environment locked coin toss
                        env_locked_coin_toss = self.task.world[next_y][next_x] == '.'
                        if( coin_toss != env_locked_coin_toss ):
                            raise CoinFlipMismatchError

                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("front_is_clear=true")
                    else:
                        self.state_sequence.append("front_is_clear=false")
            
            # to store state_sequence when run in synthesis mode
            # synthesis mode
            else:
                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("front_is_clear=true")
                    else:
                        self.state_sequence.append("front_is_clear=false")           

        return self.task.world[next_y][next_x] == '.'


    def _front_is_clear_for_move(self):
        next_x = self.task.agent.position[0] + self.task.agent.facing[0]
        next_y = self.task.agent.position[1] + self.task.agent.facing[1]
        new_loc = str(next_y) + "#" + str(next_x)

        # max x in 2D real world corresponds to max column index = width of world
        if( (next_x >= self.width) or (next_y >= self.height) ):
            raise AgentOutOfBoundsError
        else:
            # union of set a and set b in python code is "a | b"
            if( self.mode == "inverse" ):
                if( new_loc not in ( self.locked_empty_cells | self.locked_wall_cells | self.locked_marker_cells ) ):
                    # if new_loc is an unlocked empty cell, that cell is always assigned empty
                    # front is always clear for a move condition to an empty unlocked cell
                    self.locked_empty_cells.add(new_loc)
                    self.state_sequence.append("front_is_clear_for_move=true")
                    self.task.world[next_y][next_x] = '.'

                else:
                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("front_is_clear_for_move=true")
                    else:
                        self.state_sequence.append("front_is_clear_for_move=false")
            # to store state_sequence when run in synthesis mode
            # synthesis mode
            else:
                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("front_is_clear_for_move=true")
                    else:
                        self.state_sequence.append("front_is_clear_for_move=false")           

        return self.task.world[next_y][next_x] == '.'


    # defining world condition checks in environment
    @world_condition
    def front_is_not_clear(self):
        '''Check front is clear'''
        return self._front_is_not_clear()


    def _front_is_not_clear(self):
        next_x = self.task.agent.position[0] + self.task.agent.facing[0]
        next_y = self.task.agent.position[1] + self.task.agent.facing[1]
        new_loc = str(next_y) + "#" + str(next_x)

        if( not self.record_func_call() ):
            raise ExecutionTimeoutError
        # max x in 2D real world corresponds to max column index = width of world
        elif( (next_x >= self.width) or (next_y >= self.height) ):
            raise AgentOutOfBoundsError
        else:
            if( self.mode == "inverse" ):
                # get a coin flip
                if( self.coin_flips != None ):
                    if( self.coin_flip_idx < len(self.coin_flips) ):
                        coin_toss = self.coin_flips[self.coin_flip_idx]
                        self.coin_flip_idx += 1
                    else:
                        # this exception should logically never be thrown
                        raise ExceededPreFlippedCoinsError                        
                else:
                    coin_toss = np.random.choice([0, 1], p=[self.prob_front_is_clear, 1-self.prob_front_is_clear])

                if( new_loc not in ( self.locked_empty_cells | self.locked_wall_cells | self.locked_marker_cells ) ):
                    if( coin_toss ):
                        self.locked_wall_cells.add(new_loc)
                        self.state_sequence.append("front_is_not_clear=true")
                        self.task.world[next_y][next_x] = '#'
                    else:
                        self.locked_empty_cells.add(new_loc)
                        self.state_sequence.append("front_is_not_clear=false")
                        self.task.world[next_y][next_x] = '.'
                
                else:
                    # check if in mcts inverse mode
                    if( self.coin_flips != None ):
                        # check for coin flip mismatch
                        # mcts intended coin toss doesn't match environment locked coin toss
                        env_locked_coin_toss = (self.task.world[next_y][next_x] == '#')
                        if( coin_toss != env_locked_coin_toss ):
                            raise CoinFlipMismatchError

                    if( self.task.world[next_y][next_x] == '#' ):
                        self.state_sequence.append("front_is_not_clear=true")
                    else:
                        self.state_sequence.append("front_is_not_clear=false")
            
            # to store state_sequence when run in synthesis mode
            # synthesis mode
            else:
                    if( self.task.world[next_y][next_x] == '#' ):
                        self.state_sequence.append("front_is_not_clear=true")
                    else:
                        self.state_sequence.append("front_is_not_clear=false")           

        return self.task.world[next_y][next_x] == '#'


    @world_condition
    def left_is_clear(self):
        '''Check left is clear'''
        return self._left_is_clear()


    # todo check logic is correct
    def _left_is_clear(self):
        next_x = self.task.agent.position[0] + self.task.agent.facing[1]
        next_y = self.task.agent.position[1] - self.task.agent.facing[0]
        new_loc = str(next_y) + "#" + str(next_x)
        
        if( not self.record_func_call() ):
            raise ExecutionTimeoutError
        else:
            if( self.mode == "inverse" ):
                # get a coin flip
                if( self.coin_flips != None ):
                    if( self.coin_flip_idx < len(self.coin_flips) ):
                        coin_toss = self.coin_flips[self.coin_flip_idx]
                        self.coin_flip_idx += 1
                    else:
                        # this exception should logically never be thrown
                        raise ExceededPreFlippedCoinsError
                else:
                    coin_toss = np.random.choice([0, 1], p=[1-self.prob_left_is_clear, self.prob_left_is_clear])

                if( new_loc not in ( self.locked_empty_cells | self.locked_wall_cells | self.locked_marker_cells ) ):                    
                    if( coin_toss ):
                        self.locked_empty_cells.add(new_loc)
                        self.state_sequence.append("left_is_clear=true")
                        self.task.world[next_y][next_x] = '.'
                    else:
                        self.locked_wall_cells.add(new_loc)
                        self.state_sequence.append("left_is_clear=false")
                        self.task.world[next_y][next_x] = '#'
                
                else:
                    # check if in mcts inverse mode
                    if( self.coin_flips != None ):
                        # check for coin flip mismatch
                        # mcts intended coin toss doesn't match environment locked coin toss
                        env_locked_coin_toss = self.task.world[next_y][next_x] == '.'
                        if( coin_toss != env_locked_coin_toss ):
                            raise CoinFlipMismatchError

                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("left_is_clear=true")
                    else:
                        self.state_sequence.append("left_is_clear=false")
            
            else:
                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("left_is_clear=true")
                    else:
                        self.state_sequence.append("left_is_clear=false")            

        
        return self.task.world[next_y][next_x] == '.'


    @world_condition
    def right_is_clear(self):
        '''Check right is clear'''
        return self._right_is_clear()

    # todo check logic is correct
    def _right_is_clear(self):
        next_x = self.task.agent.position[0] - self.task.agent.facing[1]
        next_y = self.task.agent.position[1] + self.task.agent.facing[0]
        new_loc = str(next_y) + "#" + str(next_x)
        
        if( not self.record_func_call() ):
            raise ExecutionTimeoutError
        else:
            if( self.mode == "inverse" ):
                # get a coin flip
                if( self.coin_flips != None ):
                    if( self.coin_flip_idx < len(self.coin_flips) ):
                        coin_toss = self.coin_flips[self.coin_flip_idx]
                        self.coin_flip_idx += 1
                    else:
                        # this exception should logically never be thrown
                        raise ExceededPreFlippedCoinsError
                else:
                    coin_toss = np.random.choice([0, 1], p=[1-self.prob_right_is_clear, self.prob_right_is_clear])

                if( new_loc not in ( self.locked_empty_cells | self.locked_wall_cells | self.locked_marker_cells ) ):    
                    if( coin_toss ):
                        self.locked_empty_cells.add(new_loc)
                        self.state_sequence.append("right_is_clear=true")
                        self.task.world[next_y][next_x] = '.'
                    else:
                        self.locked_wall_cells.add(new_loc)
                        self.state_sequence.append("right_is_clear=false")
                        self.task.world[next_y][next_x] = '#'
                
                else:
                    # check if in mcts inverse mode
                    if( self.coin_flips != None ):
                        # check for coin flip mismatch
                        # mcts intended coin toss doesn't match environment locked coin toss
                        env_locked_coin_toss = self.task.world[next_y][next_x] == '.'
                        if( coin_toss != env_locked_coin_toss ):
                            raise CoinFlipMismatchError

                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("right_is_clear=true")
                    else:
                        self.state_sequence.append("right_is_clear=false")
            
            else:
                    if( self.task.world[next_y][next_x] == '.' ):
                        self.state_sequence.append("right_is_clear=true")
                    else:
                        self.state_sequence.append("right_is_clear=false")            

        return self.task.world[next_y][next_x] == '.'


    # defining states of environment using @property decorator
    # https://www.programiz.com/python-programming/property
    @property
    def facing_north(self):
        return self.task.agent.facing[1] == -1

    @property
    def facing_south(self):
        return self.task.agent.facing[1] == 1

    @property
    def facing_west(self):
        return self.task.agent.facing[0] == -1

    @property
    def facing_east(self):
        return self.task.agent.facing[0] == 1

    @property
    def facing_idx(self):
        if self.facing_north: # (0, -1)
            return 0
        elif self.facing_south: # (0, 1)
            return 1
        elif self.facing_west: # (-1, 0)
            return 2
        elif self.facing_east: # (1, 0)
            return 3


    # todo - is this the best way to integrate state function in our class hierarchy?
    # Get the state of the environment - state data is stored in task class
    # This method is not overridden in EnvironmentHoc, so a call using an EnvironmentHoc object
    # will fall back and use this function definition in base class.
    # However, this method is overriden in EnvironmentKarel and a call
    # using an EnvironmentKarel object will use the function definition in derived class.
    @property
    def state(self):
        """
            0: Hero facing North
            1: Hero facing South
            2: Hero facing West
            3: Hero facing East
            4: Wall
            5: Empty / 0 marker
        """
        state = self.task.zero_state.copy()
        state[:,:,5] = 1

        # 0 ~ 3: Hero facing North, South, West, East
        x, y = self.task.agent.position
        state[y, x, self.facing_idx] = 1

        # 4: wall or not
        for jdx, row in enumerate(self.task.world):
            for idx, char in enumerate(row):
                if char == self.WALL_CHAR:
                    state[jdx][idx][4] = 1
                # todo why need this when all cells are initialized with state 5
                # maybe written just to make it explicit
                # todo: why is "char == self.WALL_CHAR" repeated in elif also?
                elif char == self.WALL_CHAR or char in self.AGENT_CHARS:
                    state[:,:,5] = 1

        return state


    # The design philosophy for run() is similar to RL, run program on task is
    # the only current function which requires interaction among class objects.
    # Placing the run() function in Environment class to implement a similar design
    # to RL, where an Environment object with its state stored in Task object
    # is called with a Code object (agent's policy of actions), and updates its containing
    # Task object to reflect the final state after program execution (sequence of step() calls
    # to the environment in OpenAI gym).
    def run(self, program, with_timeout=False, **kwargs):
        code_hash = hash(program.code)
        program.dsl.call_counter = [0]

        if code_hash in program.dsl.parser.funct_table:
            def fn():
                return program.dsl.parser.funct_table[code_hash]()
        else:
            yacc = program.dsl.parser.yacc
            def fn():
                # passing self (Environment object) for parser to call functions on,
                # which modify the state of the Environment stored in Task object.
                
                # todo : can we try to solve using the original idea of passing an env 
                # object in the yacc.parse call? yacc.parse(program.code, self, **kwargs)()
                # the issue here was an error that the p function in yacc take only 2 arguments
                return yacc.parse(program.code, **kwargs)()
            program.dsl.parser.funct_table[code_hash] = fn

        # todo the function call fn() modifies the state of the environment?
        # todo what is contained in the return value out?
        out = fn()
        return out


    def inverse_run(self, program, with_timeout=False, **kwargs):

        yacc = program.dsl.parser.yacc
        def fn():
            # passing self (Environment object) for parser to call functions on,
            # which modify the state of the Environment stored in Task object.
            
            # todo : can we try to solve using the original idea of passing an env 
            # object in the yacc.parse call? yacc.parse(program.code, self, **kwargs)()
            # the issue here was an error that the p function in yacc take only 2 arguments
            return yacc.parse(program.code, **kwargs)()

        # todo the function call fn() modifies the state of the environment?
        # todo what is contained in the return value out?
        out = fn()
        return out


    # virtual method
    def draw(self, prefix="", skip_number=False, with_color=False, no_print=False):
        # this method should be overrided in derived classes
        raise NotImplementedError()


    # todo border mask defined non class function outside but border_mask_inverse defined inside class
    def border_mask_inverse(self, array, value):
        array[0,:], array[-1,:], array[:,0], array[:,-1] = value, value, value, value
        [self.locked_wall_cells.add(str(j) + '#' + str(0)) for j in range(self.width)]
        [self.locked_wall_cells.add(str(j) + '#' + str(self.height-1)) for j in range(self.width)]
        [self.locked_wall_cells.add(str(0) + '#' + str(i)) for i in range(self.height)]
        [self.locked_wall_cells.add(str(self.width-1) + '#' + str(i)) for i in range(self.height)]


    def record_func_call(self):
        self.num_func_calls += 1
        if( self.num_func_calls > self.max_func_calls ):
            return False
        return True


    # yacc will use these names to call above functions
    bool_path_ahead = front_is_clear
    bool_no_path_ahead = front_is_not_clear
    bool_path_left = left_is_clear
    bool_path_right = right_is_clear

    # todo these are not used?
    turnRight = turn_right
    turnLeft = turn_left
