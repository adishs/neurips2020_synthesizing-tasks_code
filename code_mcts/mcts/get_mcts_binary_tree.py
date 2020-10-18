from mcts.mcts_tree_node import MctsTreeNode


# ----------------------------------
# tree creation on the fly
# ----------------------------------

def get_loc_nodes_onthefly(parent_node, use_subtree_flag):
	if( use_subtree_flag ):
		direction_choices = ["fixed_loc_dir"]
	else:
		direction_choices = get_direction_choices()
	loc_nodes = []
	for dir in direction_choices:
		loc_node = MctsTreeNode( node_type="loc", parent=parent_node, children=[], val=dir, depth=(parent_node.depth+1) )
		loc_nodes.append(loc_node)

	return loc_nodes


# type-1 tree


def grow_root(root, max_depth):
	# add 20 location children nodes or 1 loc node if agentloc and agentdir is fixed
	loc_nodes = get_loc_nodes_onthefly(root, use_subtree_flag=False)
	root.children = loc_nodes


def grow_type1_loc(node, max_depth):
	pass


# type-2 tree


def grow_type2_loc(node, max_depth):
	# add while nodes
	while_node_1 = MctsTreeNode( node_type="while1", parent=node, children=[], val=1, depth=(node.depth+1) )
	while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
	node.children = [while_node_1, while_node_0]


def grow_type2_while0(node, max_depth):
	# while0 node is a terminating leaf node with no children
	pass


def grow_type2_while1(node, max_depth):
	if( node.depth < max_depth ):
		# add while nodes
		while_node_1 = MctsTreeNode( node_type="while1", parent=node, children=[], val=1, depth=(node.depth+1) )
		while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [while_node_1, while_node_0]
	else:
		# add terminating while0 node
		while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [while_node_0]


# type-3 tree


def grow_type3_loc(node, max_depth):
	# add while nodes
	while_node_1 = MctsTreeNode( node_type="while1", parent=node, children=[], val=1, depth=(node.depth+1) )
	while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
	node.children = [while_node_1, while_node_0]


def grow_type3_while0(node, max_depth):
	# while0 node is a terminating leaf node with no children
	pass


def grow_type3_while1(node, max_depth):
	# add if nodes
	if_node_1 = MctsTreeNode( node_type="if1", parent=node, children=[], val=1, depth=(node.depth+1) )
	if_node_0 = MctsTreeNode( node_type="if0", parent=node, children=[], val=0, depth=(node.depth+1) )
	node.children = [if_node_1, if_node_0]


def grow_type3_if0(node, max_depth):
	if( node.depth < max_depth ):
		# add while nodes
		while_node_1 = MctsTreeNode( node_type="while1", parent=node, children=[], val=1, depth=(node.depth+1) )
		while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [while_node_1, while_node_0]
	else:
		# add terminating while0 node
		while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [while_node_0]


def grow_type3_if1(node, max_depth):
	if( node.depth < max_depth ):
		# add while nodes
		while_node_1 = MctsTreeNode( node_type="while1", parent=node, children=[], val=1, depth=(node.depth+1) )
		while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [while_node_1, while_node_0]
	else:
		# add terminating while0 node
		while_node_0 = MctsTreeNode( node_type="while0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [while_node_0]	


# type-5 tree

def grow_type5_loc(node, max_depth):
	# add if nodes
	if_node_1 = MctsTreeNode( node_type="if1", parent=node, children=[], val=1, depth=(node.depth+1) )
	if_node_0 = MctsTreeNode( node_type="if0", parent=node, children=[], val=0, depth=(node.depth+1) )
	node.children = [if_node_1, if_node_0]


def grow_type5_if0(node, max_depth):
	if( node.depth < max_depth ):
		# add if nodes
		if_node_1 = MctsTreeNode( node_type="if1", parent=node, children=[], val=1, depth=(node.depth+1) )
		if_node_0 = MctsTreeNode( node_type="if0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [if_node_1, if_node_0]


def grow_type5_if1(node, max_depth):
	if( node.depth < max_depth ):
		# add if nodes
		if_node_1 = MctsTreeNode( node_type="if1", parent=node, children=[], val=1, depth=(node.depth+1) )
		if_node_0 = MctsTreeNode( node_type="if0", parent=node, children=[], val=0, depth=(node.depth+1) )
		node.children = [if_node_1, if_node_0]

		
# ----------------------------------


def get_tree_type(program_id):
	program_id_to_mcts_tree_type = {
		"hoc-A" : "type-1",
		"hoc-B" : "type-1",
		"hoc-C" : "type-1",
		"hoc-D" : "type-1",
		"hoc-E" : "type-1",
		"hoc-F" : "type-2",
		"hoc-G" : "type-3",
		"hoc-H" : "type-3",
		"hoc-J" : "type-3",
		"hoc-I" : "type-4",
		"hoc-K" : "type-4",
		"hoc-L" : "type-4",
		"karel-A" : "type-1",
		"karel-B" : "type-1",
		"karel-C" : "type-1",
		"karel-D" : "type-1",
		"karel-F" : "type-2",
		"karel-I" : "type-3",
		"karel-J" : "type-4",
		"karel-E" : "type-5",
		"karel-G" : "type-6",
		"karel-H" : "type-7"
	}

	return program_id_to_mcts_tree_type[program_id]


def get_loc_nodes(parent_node, tree_type, use_subtree_flag):
	if( use_subtree_flag ):
		direction_choices = ["fixed_loc_dir"]
	else:
		direction_choices = get_direction_choices(tree_type)
	loc_nodes = []
	for dir in direction_choices:
		loc_node = MctsTreeNode(parent=parent_node, children=[], val=dir)
		loc_nodes.append(loc_node)

	return loc_nodes


def get_direction_choices():
	'''
	if( tree_type == "type-4" ):
		direction_choices = ["1N", "1E", "1S", "1W"]
	else:
	'''
	direction_choices = []
	for i in range(1, 6):
		for dir in ["N", "E", "S", "W"]:
			direction_choices.append(str(i)+dir)

	return direction_choices


def get_tree_gen_func(tree_type):
	type_to_tree_gen_func = {
		"type-1" : add_binary_tree_1,
		"type-2" : add_binary_tree_2,
		"type-3" : add_binary_tree_3,
		"type-4" : add_binary_tree_4,
		"type-5" : add_binary_tree_5,
		"type-6" : add_binary_tree_6,
		"type-7" : add_binary_tree_7,
	}

	return type_to_tree_gen_func[tree_type]


def generate_bin_tree(tree_type, depth, use_subtree_flag):
	num_leafs = [0]
	# create root node
	root = MctsTreeNode(parent=None, children=[], val="root")

	# add 20 location children nodes or 1 loc node is agentloc and agentdir is fixed
	loc_nodes = get_loc_nodes(root, tree_type, use_subtree_flag)
	root.children = loc_nodes
	# add binary tree for each loc node
	for loc_node in root.children:
		get_tree_gen_func(tree_type)(depth=depth, parent_nodes=[loc_node], num_leafs=num_leafs)
		print("created tree for {}".format(loc_node.val))

	return root, num_leafs[0]


def add_binary_tree_1(depth, parent_nodes, num_leafs):
	# add each loc_node as leaf node
	num_leafs[0] += 1


def add_binary_tree_2(depth, parent_nodes, num_leafs):
	parent_node = parent_nodes[0]
	for i in range(depth):
		#print("creating depth {} of mcts tree".format(i))
		parent_node = add_binary_tree_block_2(parent_node, num_leafs)
	
	# add terminating while nodes
	terminate_while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [terminate_while_node_0]
	# add terminate_while_node_0 as leaf node
	num_leafs[0] += 1


def add_binary_tree_block_2(parent_node, num_leafs):
	# add while nodes
	while_node_1 = MctsTreeNode(parent=parent_node, children=[], val=1)
	while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [while_node_1, while_node_0]
	# add while_node_0 as leaf node
	num_leafs[0] += 1

	next_parent_node = while_node_1
	
	return next_parent_node


def add_binary_tree_3(depth, parent_nodes, num_leafs):
	for i in range(depth):
		#print("creating depth {} of mcts tree".format(i))
		next_parent_nodes = []
		for parent_node in parent_nodes:
			next_parent_nodes += add_binary_tree_block_3(parent_node, num_leafs)
		parent_nodes = next_parent_nodes
	# add terminating while nodes
	for parent_node in parent_nodes:
		terminate_while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
		parent_node.children = [terminate_while_node_0]
		# add terminate_while_node_0 as leaf node
		num_leafs[0] += 1


def add_binary_tree_block_3(parent_node, num_leafs):
	# add while nodes
	while_node_1 = MctsTreeNode(parent=parent_node, children=[], val=1)
	while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [while_node_1, while_node_0]
	# add while_node_0 as leaf node
	num_leafs[0] += 1
	# add if nodes
	if_node_1 = MctsTreeNode(parent=while_node_1, children=[], val=1)
	if_node_0 = MctsTreeNode(parent=while_node_1, children=[], val=0)
	while_node_1.children = [if_node_1, if_node_0]

	next_parent_nodes = [if_node_1, if_node_0]
	
	return next_parent_nodes


def add_binary_tree_4(depth, parent_nodes, num_leafs):
	for i in range(depth):
		#print("creating depth {} of mcts tree".format(i))
		next_parent_nodes = []
		for parent_node in parent_nodes:
			#print(parent_node.name)
			next_parent_nodes += add_binary_tree_block_4(parent_node, num_leafs)
		parent_nodes = next_parent_nodes
	# add terminating while nodes
	for parent_node in parent_nodes:
		terminate_while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
		parent_node.children = [terminate_while_node_0]
		# add terminate_while_node_0 as leaf node
		num_leafs[0] += 1


def add_binary_tree_block_4(parent_node, num_leafs):
	# add while nodes
	while_node_1 = MctsTreeNode(parent=parent_node, children=[], val=1)
	while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [while_node_1, while_node_0]
	# add while_node_0 as leaf node
	num_leafs[0] += 1
	# add a nodes
	a_node_1 = MctsTreeNode(parent=while_node_1, children=[], val=1)
	a_node_0 = MctsTreeNode(parent=while_node_1, children=[], val=0)
	while_node_1.children = [a_node_1, a_node_0]
	# add bc nodes
	bc_node_1 = MctsTreeNode(parent=a_node_0, children=[], val=1)
	bc_node_0 = MctsTreeNode(parent=a_node_0, children=[], val=0)
	a_node_0.children = [bc_node_1, bc_node_0]

	next_parent_nodes = [a_node_1, bc_node_1, bc_node_0]
	
	return next_parent_nodes


def add_binary_tree_5(depth, parent_nodes, num_leafs):
	for i in range(depth):
		#print("creating depth {} of mcts tree".format(i))
		next_parent_nodes = []
		for parent_node in parent_nodes:
			next_parent_nodes += add_binary_tree_block_5(parent_node)
		parent_nodes = next_parent_nodes
	# add last layer nodes as leafs
	for terminal_node in parent_nodes:
		num_leafs[0] += 1


def add_binary_tree_block_5(parent_node):
	# add if nodes
	if_node_1 = MctsTreeNode(parent=parent_node, children=[], val=1)
	if_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [if_node_1, if_node_0]

	next_parent_nodes = [if_node_1, if_node_0]
	
	return next_parent_nodes


def add_binary_tree_6(depth, parent_nodes, num_leafs): 
	parent_node = parent_nodes[0]
	# process while_loop_1
	while_2_parent_nodes = []
	for i in range(depth):
		#print("creating depth {} of loop1 of mcts tree".format(i))
		parent_node, while_node_0 = add_binary_tree_block_6(parent_node)
		while_2_parent_nodes.append(while_node_0)
	
	# add terminating while_loop_1 nodes
	terminate_while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [terminate_while_node_0]	
	while_2_parent_nodes.append(terminate_while_node_0)

	# process while_loop_2
	for parent_node in while_2_parent_nodes:
		for i in range(depth):
			#print("creating depth {} of loop2 of mcts tree".format(i))
			parent_node, _ = add_binary_tree_block_6(parent_node)	
		
		# add terminating while_loop_2 nodes
		terminate_while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
		parent_node.children = [terminate_while_node_0]		
		# add terminating while_loop_2 nodes as leaf nodes
		num_leafs[0] += 1


def add_binary_tree_block_6(parent_node):
	# add while nodes
	while_node_1 = MctsTreeNode(parent=parent_node, children=[], val=1)
	while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [while_node_1, while_node_0]

	next_parent_node = while_node_1
	
	return next_parent_node, while_node_0	


def add_binary_tree_7(depth, parent_nodes, num_leafs):
	while_nodes_0 = []
	for i in range(depth):
		#print("creating depth {} of mcts tree".format(i))
		next_parent_nodes = []
		for parent_node in parent_nodes:
			next_parent_nodes_new, while_node_0_new = add_binary_tree_block_7(parent_node)
			next_parent_nodes += next_parent_nodes_new
			while_nodes_0 += while_node_0_new
		parent_nodes = next_parent_nodes
	
	# add terminating while nodes
	terminate_while_nodes_0 = []
	for parent_node in parent_nodes:
		terminate_while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
		parent_node.children = [terminate_while_node_0]
		terminate_while_nodes_0.append(terminate_while_node_0)
	
	# append last if node to while_nodes_0 and terminate_while_node_0
	for node in (while_nodes_0 + terminate_while_nodes_0):
		if_node_1 = MctsTreeNode(parent=node, children=[], val=1)
		if_node_0 = MctsTreeNode(parent=node, children=[], val=0)	
		node.children = [if_node_1, if_node_0]
		# add if_node_1 and if_node_0 as leaf nodes
		num_leafs[0] += 2



def add_binary_tree_block_7(parent_node):
	# add while nodes
	while_node_1 = MctsTreeNode(parent=parent_node, children=[], val=1)
	while_node_0 = MctsTreeNode(parent=parent_node, children=[], val=0)
	parent_node.children = [while_node_1, while_node_0]
	
	# add if nodes
	if_node_1 = MctsTreeNode(parent=while_node_1, children=[], val=1)
	if_node_0 = MctsTreeNode(parent=while_node_1, children=[], val=0)
	while_node_1.children = [if_node_1, if_node_0]

	next_parent_nodes = [if_node_1, if_node_0]
	
	return next_parent_nodes, [while_node_0]

