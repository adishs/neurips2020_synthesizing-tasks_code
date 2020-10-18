'''
code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

import ply.lex as lex

from utilities import yacc
from utilities.utils import get_rng


class _Parser(object):
    # todo why are tokens and precedence declared as class attributes 
    # rather than instance attributes in __init__
    tokens = ()
    precedence = ()

    def __init__(self, rng=None, min_int=0, max_int=19, debug=False, env=None, **kwargs):
        # Build the lexer and parser
        modname = self.__class__.__name__
        self.lexer = lex.lex(module=self, debug=debug)
        self.yacc, self.grammar = yacc.yacc(
                module=self,
                debug=debug,
                tabmodule="_parsetab",
                with_grammar=True)

        # todo mostly grammar production rules are here
        self.prodnames = self.grammar.Prodnames

        # repeating instance attributes common to dsl and parser
        # todo can we implement this in a better way without repeating?
        # having a pointer to dsl class back from parser class just for
        # these attributes seems too much
        self.min_int = min_int
        self.max_int = max_int
        self.rng = get_rng(rng)

        # reference to env object - required when a program needs to be executed on a task
        # can be None the rest of the time
        self.env = None

        self.flush_hit_info()


    def flush_hit_info(self):
        self.hit_info = {}
        self.funct_table = {} # save parsed function
        self.counter = 0
        self.symbolic_decisions = []


def dummy():
    pass

