import simpy
import rendezvousPoint
import flow
import membrane

class Node:
	def __init__(self, env):
		self.env = env
		self.parent_rp = [] # all Rendezvous Points that the node is connected to
		self.child_rp = [] # all Rendezvous Points that are created/owned by the node
		self.cspace = [] # all Flows the node can send on
		self.listener = [] # all Flows the node is listening on
		self.node_cap = [] # all the Nodes it hold capabilities to
		self.my_membrane = None # membranes it inherits or creates
		self.membrane = []
		#self.blocker = False
	
	def createNode(self, new_node):
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self) 
		yield new_rp.rp.request() # Request for parent node to acquire one end of the RP
		new_node.parent_rp.append(new_rp) # RP assigned to new node
		self.child_rp.append(new_rp)
		#print(self.child_rp)
		new_node.my_membrane = self.my_membrane
		new_rp.membrane.append(self.my_membrane)

	def createFlow(self, flow_specs): 
		new_flow = flow.Flow(self.env, flow_specs) 
		#yield new_flow.flow.request() # To be done at sender; Flow requested by the node
		self.cspace.append(new_flow) # Add flow to CSpace of the node
		new_rp.membrane.append(self.my_membrane)
		#print(new_flow)

	def createRendezvousPoint(self):
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self)
		self.child_rp.append(new_rp)
		new_rp.membrane.append(self.my_membrane)
		yield new_rp.rp.request() # Request for parent node to acquire one end of the RP
		print(self.child_rp[0])
		#print(self.child_rp[0].rp)

	def createMembrane(self):
		new_membrane = membrane.Membrane(self.env, self)
		self.my_membrane = new_membrane
		yield new_membrane.membrane_rsc.request()
		print(self.my_membrane)
		
	def releaseRP(self, rp_n):
		yield rp_n.rp.release()

	def sendCap(self, cap_receiver):
		yield self.env.timeout(2)
		if self.my_membrane not in cap_receiver.child_rp[0].membrane:
			self.my_membrane.wrap(cap_receiver.child_rp[0], cap_receiver)
		cap_receiver.child_rp[0].put(self.child_rp[0])
		#self.env.process(cap_receiver.recvCap(rp))
		print("Send {0} through {1} from {2} to {3}".format(self.child_rp[0], cap_receiver.child_rp[0], self, cap_receiver))
	
	def recvCap(self):
		rp_recv = self.child_rp[0].get_output_conn()
		cap = yield rp_recv.get()
		print("Received {0} at {1}".format(cap, self))
		if self.child_rp[0].init_node == self:
			self.my_membrane.unwrap(cap, self)
		cap_type = cap.__class__.__name__ #type(cap).__name__
		print("Capability type: {0} ".format(cap_type))
		if cap_type == "RendezvousPoint":
			self.parent_rp.append(cap)
		elif cap_type == "Flow":
			self.cspace.append(cap)
			cap.addSender(self)
		elif cap_type == "Node":
			self.node_cap.append(cap)

	#def sendCap(self):
        #        self.cspace[0].put('test') # Send message on flow 
        #        self.env.process(self.recvCap()) # schedule receive
	#
        #def recvCap(self):
        #        msg = yield self.cspace[0].get() # Get value from flow
        #        print(msg)
	
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
			#self.env.process(reset_node.releaseRP(p_rp))
			parent_node = p_rp.init_node
			parent_node.child_rp.remove(p_rp)
			#self.env.process(parent_node.releaseRP(p_rp))
			
		reset_node.parent_rp = []
		
		for c_rp in reset_node.child_rp:
			child_node = c_rp.attached_node
			if child_node is not None:
				self.env.process(c_rp.detachNode())
				child_node.parent_rp.remove(c_rp)
				#self.env.process(child_node.releaseRP(c_rp))
			self.env.process(reset_node.releaseRP(c_rp))

		reset_node.child_rp = []

		self.env.process(reset_node.revoke())

		for l in reset_node.listener:
			self.env.process(l.callback())

		reset_node.listener = []

		self.env.process(take(reset_node))

	def take(self, n):
		self.env.process(createNode(n))
