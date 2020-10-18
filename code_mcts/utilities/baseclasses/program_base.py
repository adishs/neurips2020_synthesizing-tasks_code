'''
code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

class Program(object):
    def __init__(self, code=None, dsl=None):
        self.code = code
        self.dsl = dsl

    # Other functions will be added similar to RLNPS code
    # for AST to json tokens, AST to pytorch tensor, etc