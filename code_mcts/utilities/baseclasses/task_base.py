'''
code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

# Implementing composition relationship between Environment and Task classes, i.e., 
# a task object cannot exist without its container, an Environment object.
# Note: Python doesn't enforce hiding, more of a stylistic nomenclature to inform developers of intended usage 
# https://stackoverflow.com/questions/28528118/how-to-move-code-of-an-inner-class-to-different-file-python
# Leading underscore is used to signify "_Task" is a private nested class
class _Task(object):
    def __init__(self, world=None, agent=None):
        self.world = world
        self.agent = agent
