import simpy

class RendezvousPointState:
	def __init__(self, env, init_node):
		self.env = env
		self.parent_node = init_node
		self.child_node = None
		// create "rendezvousPoint" container with cap 2 and add element in queue
