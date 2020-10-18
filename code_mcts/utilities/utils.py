'''
code based on https://github.com/carpedm20/karel, 
and https://github.com/alts/karel
'''

import numpy as np
import random
import os
import errno
import signal
from functools import wraps
from pyparsing import nestedExpr


class CoinFlipMismatchError(Exception):
    pass


class ExceededPreFlippedCoinsError(Exception):
    pass

    
class UnknownMctsTreeTypeError(Exception):
    pass


class PutMaxMarkerError(Exception):
    pass


class PickEmptyMarkerError(Exception):
    pass


class WallCrashError(Exception):
    pass


class AgentBacktrackingError(Exception):
    pass


class AgentOutOfBoundsError(Exception):
    pass


class ExecutionTimeoutError(Exception):
    pass


# keeping seed as None to different output for different executions
# if seed is None, data from /dev/urandom or clock is read as seed
def get_rng(rng, seed=None):
    if rng is None:
        rng = np.random.RandomState(seed)
    return rng


def get_hash():
    return random.getrandbits(128)


def dummy():
    pass


def str2bool(v):
    return v.lower() in ('true', '1')


# todo understand timeout code
def timeout(seconds=10, error_message=os.strerror(errno.ETIME)):
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.setitimer(signal.ITIMER_REAL,seconds) #used timer instead of alarm
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result
        return wraps(func)(wrapper)
    return decorator


def beautify_fn(inputs, indent=1, tabspace=2):
    lines, queue = [], []
    space = tabspace * " "

    for item in inputs:
        if item == ";":
            lines.append(" ".join(queue))
            queue = []
        elif type(item) == str:
            queue.append(item)
        else:
            lines.append(" ".join(queue + ["{"]))
            queue = []

            inner_lines = beautify_fn(item, indent=indent+1, tabspace=tabspace)
            lines.extend([space + line for line in inner_lines[:-1]])
            lines.append(inner_lines[-1])

    if len(queue) > 0:
        lines.append(" ".join(queue))

    return lines + ["}"]


def pprint(code, *args, **kwargs):
    print(beautify(code, *args, **kwargs))


# todo understand beautify code
def beautify(code, tabspace=2):
    code = " ".join(replace_dict.get(token, token) for token in code.split())
    array = nestedExpr('{','}').parseString("{"+code+"}").asList()
    lines = beautify_fn(array[0])
    return "\n".join(lines[:-1]).replace(' ( ', '(').replace(' )', ')')


def makedirs(path):
    if not os.path.exists(path):
        print(" [*] Make directories : {}".format(path))
        os.makedirs(path)


