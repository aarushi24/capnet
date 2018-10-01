import simpy

class RendezvousPoint:
	def __init__(self, env, parent_node):
		self.init_node = parent_node
		#self.attached_node = None
		# create rp container
		self.rp = simpy.Resource(env, capacity=1)
		self.membrane = []
