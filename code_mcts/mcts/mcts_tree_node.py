class MctsTreeNodeCompressed(object):
	def __init__(self, parent=None, children=[],
				val=None):
		# mcts attributes
		self.parent = parent
		self.children = children
		self.val = val
		self.compressed = True


class MctsTreeNode(object):
	def __init__(self, node_type=None, parent=None, children=[],
				val=None, name="", depth=None):
		# mcts attributes
		self.node_type = node_type
		self.parent = parent
		self.children = children
		self.depth = depth
		self.avg_score = 0
		self.num_iterations = 0
		self.grown = False
		# metainfo attributes
		self.num_picked = 0
		# val stores coin flip value
		self.val = val
		# validity check: None (unknown) / True / False
		self.valid = None
		# bfs attributes
		#self.colour = "white"
		# feature scoring
		self.score_dict = {}
		# pruning
		self.is_minimal_delta_debug = None
		self.is_minimal_shortest_path = None