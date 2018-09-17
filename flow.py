import simpy

class Flow:
	def __init__(self, env, flow_specs):
		self.recv = None
		self.flow_specs = flow_specs # define its own class
		# create flow resource with cap 1
		self.flow = simpy.Resource(env, capacity=1)

	def mint(self, flow_specs):
		sub_flow = Flow(self.env, self.source, flow_specs)

	def addRecv(self, recv_node):
		self.recv = recv_node

	def callback(self):
		self.recv = None
