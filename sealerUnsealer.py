import simpy

class SealerUnsealer:
	def __init__(self, env, parent_node):
		self.env = env
		self.init_node = parent_node
