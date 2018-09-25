import simpy
import rendezvousPoint
import flow

class Node:
	def __init__(self, env):
		self.env = env
		self.parent_rp = [] # all Rendezvous Points that the node is connected to
		self.child_rp = [] # all Rendezvous Points that are created/owned by the node
		self.cspace = [] # all Flows the node can send on
		self.listener = [] # all Flows the node is listening on
		#self.blocker = False
	
	def createNode(self, new_node):
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self) 
		yield new_rp.rp.request() # Request for parent node to acquire one end of the RP
		self.env.process(new_node.addParent(new_rp)) # Schedule the RP assignment to new node
		self.child_rp.append(new_rp)
		#print(self.child_rp)
	
	def addParent(self, new_rp):
		self.parent_rp.append(new_rp) 
		yield new_rp.rp.request() # Request for child node to acquire other end of the RP
		new_rp.attachNode(self) # Add new node as the other end of the RP
		#print(self.parent_rp)

	def createFlow(self, flow_specs): 
		new_flow = flow.Flow(self.env, flow_specs) 
		#yield new_flow.flow.request() # To be done at sender; Flow requested by the node
		self.cspace.append(new_flow) # Add flow to CSpace of the node
		#print(new_flow)

	def createRendezvousPoint(self):
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self)
		yield new_rp.rp.request() # Request for parent node to acquire one end of the RP
		self.parent_rp.append(new_rp)
		#print(new_rp)

	def releaseRP(self, rp_n):
		yield rp_n.rp.release()

	def sendCap(self):
                #yield self.env.timeout(1)
                self.cspace[0].put('test') # Send message on flow 
                self.env.process(self.recvCap()) # schedule receive

        def recvCap(self):
                msg = yield self.cspace[0].get() # Get value from flow
                print(msg)
	
	def revoke(self):
		# Remove all flows in cspace of the node
		for c in self.cspace:
			c.callback()
		self.cspace = [] 

	def delete(self, c):
		# Remove specific flow from cspace
		c.callback()
		self.cspace.remove(c)

	def reset(self, reset_node):
		for p_rp in reset_node.parent_rp:
			self.env.process(p_rp.detachNode()) 
			self.env.process(reset_node.releaseRP(p_rp))
			parent_node = p_rp.init_node
			parent_node.child_rp.remove(p_rp)
			self.env.process(parent_node.releaseRP(p_rp))
			
		reset_node.parent_rp = []
		
		for c_rp in reset_node.child_rp:
			child_node = c_rp.attached_node
			if child_node is not None:
				self.env.process(c_rp.detachNode())
				child_node.parent_rp.remove(c_rp)
				self.env.process(child_node.releaseRP(c_rp))
			self.env.process(reset_node.releaseRP(c_rp))

		reset_node.child_rp = []

		self.env.process(reset_node.revoke())

		for l in reset_node.listener:
			self.env.process(l.callback())

		self.env.process(take(reset_node))

	def take(self, n):
		self.env.process(createNode(n))
