import simpy

class Flow:
	def __init__(self, env, source, flow_specs):
		self.env = env
		self.init_node = source
		self.sender = []
		self.flow_specs = flow_specs # TODO: define its own class
		# create flow resource with cap 1
		self.flow = simpy.Resource(self.env, capacity=2)
		self.membrane = []
		yield self.env.process(self.init_node.createFlow(self))

	def mint(self, new_sender, flow_specs):
		self.source.createFlow(sub_flow)
		# send flow cap to new sender 

	def callback(self):
		self.sender = []

	def copyCap(self, mem):
                mem.wrap(self.Flow(env, self.init_node, self.flow_specs)) # Create a copy of the flow and wrap it in the membrane
