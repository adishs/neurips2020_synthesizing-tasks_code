'''
Code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

from utilities.baseclasses.agent_base import _Agent


class _AgentKarel(_Agent):
    '''
    '''
    def __init__(self, position, facing, marker_bag=None):
        super().__init__(position, facing)
        self.marker_bag = marker_bag


    # TODO check marker functionality - can't pick from empty loc
    # and can't put if agent has no markers not implemented yet
    def holding_markers(self):
        return ( (self.marker_bag is None) or self.marker_bag > 0 )

    # TODO check marker functionality - can't pick from empty loc
    # and can't put if agent has no markers not implemented yet
    def pick_marker(self):
        if( self.marker_bag is not None):
            self.marker_bag += 1

    # TODO check marker functionality - can't pick from empty loc
    # and can't put if agent has no markers not implemented yet
    def put_marker(self):
        if( self.marker_bag is not None):
            self.marker_bag -= 1
