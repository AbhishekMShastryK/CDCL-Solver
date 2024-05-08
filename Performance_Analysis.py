from sys import argv
from pstats import *
Stats(argv[1]).strip_dirs().sort_stats(SortKey.CUMULATIVE).print_stats()