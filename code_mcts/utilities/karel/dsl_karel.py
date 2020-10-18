'''
code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

from utilities.karel.parser_karel_unified import _ParserKarelUnified
from utilities.karel.program_karel import ProgramKarel
from utilities.baseclasses.dsl_base import Dsl


class DslKarel(Dsl):
    def __init__(self, rng=None, min_int=0, max_int=19,
            max_func_call=100, debug=False, **kwargs):

        ########################
        # Build lexer and parser
        ########################
        # todo need to clean up how to use parser curly and parser synthesis
        self.parser = _ParserKarelUnified(rng, min_int, max_int, debug)
        #self.parser_curly = _ParserKarelCurly(rng, min_int, max_int, debug)
        # todo base class attributes initialized by _ParserKarelCurly are being changed 
        # by _ParserKarelSynthesis
        #self.parser_synthesis = _ParserKarelSynthesis(rng, min_int, max_int, debug)

        # todo was not able to use super().__class__.__init__ instead of current
        # Dsl.__init__
        Dsl.__init__( 
                self, rng, min_int, max_int,
                max_func_call, debug, **kwargs
        )


    # method overriding - post filtering
    def random_code(self, create_hit_info=False, *args, **kwargs):
        code = super().random_code(create_hit_info, *args, **kwargs)
        # code data is stored in respective Program class
        # todo should Program class be private and 
        # implement a composition relationship with Dsl class?
        # For now a Program class is public, a program code object is returned using a Dsl class
        # Therefore a unidirectional association from Dsl to Program class is implemented
        program = ProgramKarel(code)

        return program