import simpy

class Flow:
	def __init__(self, env, source, flow_specs):
		self.env = env
		self.source = source
		self.sender = []
		self.flow_specs = flow_specs # TODO: define its own class
		# create flow resource with cap 1
		self.flow = simpy.Resource(self.env, capacity=2)
		self.membrane = []

	def mint(self, new_sender, flow_specs):
		self.source.createFlow(sub_flow)
		# send flow cap to new sender 

	def addSender(self, recv_node):
		self.sender.append(recv_node)

	def callback(self):
		self.sender = []
