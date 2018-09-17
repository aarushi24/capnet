import simpy
import rendezvousPoint
import flow

class Node:
	def __init__(self, env):
		self.env = env
		self.parent_rp = []
		self.child_rp = []
		self.cspace = [] # Flows that it can send on
		self.listener = [] # Flows it is listening on
		#self.blocker = False
	
	def createNode(self, new_node):
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self)
		yield new_rp.rp.request()
		self.env.process(new_node.addParent(new_rp))
		new_rp.attachNode(new_node)
		self.child_rp.append(new_rp)
		#print(self.child_rp)
	
	def addParent(self, new_rp):
		self.parent_rp.append(new_rp)
		yield new_rp.rp.request()
		#print(self.parent_rp)

	def createFlow(self, flow_specs): 
		new_flow = flow.Flow(self.env, flow_specs)
		yield new_flow.flow.request()
		self.cspace.append(new_flow)
		#print(new_flow)

	def createRendezvousPoint(self):
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self)
		yield new_rp.rp.request()
		self.parent_rp.append(new_rp)
		#print(new_rp)

	def sendCap(self):
                #yield self.env.timeout(1)
                self.cspace[0].put('test')
                self.env.process(self.recvCap())

        def recvCap(self):
                msg = yield self.cspace[0].get()
                print(msg)
	
	def revoke(self):
		for c in self.cspace:
			if c.type == "flow":
				c.callback()

	def delete(self, c):
		if c.type == "flow":
			c.callback()

	#def revoke(self):
	#	for c in cspace:
	#		c.block_func.append()
