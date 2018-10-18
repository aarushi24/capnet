import simpy

class RendezvousPoint:
	def __init__(self, env, parent_node):
		self.env = env
		self.init_node = parent_node
		self.attached_nodes = []
		# create rp container
		self.rp = simpy.Resource(self.env, capacity=2)
		self.capacity = simpy.core.Infinity
		self.pipes = []
		self.membrane = []
		self.env.process(self.init_node.createRendezvousPoint(self))

	def put(self, value):
		if not self.pipes:
            		raise RuntimeError('There are no output pipes.')
        	events = [store.put(value) for store in self.pipes]
        	return self.env.all_of(events)

	def get_output_conn(self):
        	pipe = simpy.Store(self.env, capacity=self.capacity)
        	self.pipes.append(pipe)
        	return pipe
