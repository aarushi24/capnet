import simpy
import rendezvousPoint
import flow
import membrane

class Node:
	def __init__(self, env):
		self.env = env
		self.receiver_rp = [] # all Rendezvous Points that the node is connected to
		self.owner_rp = [] # all Rendezvous Points that are created/owned by the node
		self.cspace = [] # all Flows the node can send on
		self.listener = [] # all Flows the node is listening on
		self.node_cap = [] # all the Nodes it hold capabilities to
		self.node_owners = [] # all the Nodes that hold cap to it
		self.my_membrane = [] # membranes it inherits or creates
		self.membrane = []
		self.my_sealer = []
			
	def addNodeCap(self, new_node, t):
		yield self.env.timeout(t)
		self.node_cap.append(new_node)
		new_node.node_owners.append(self)
		'''
		new_rp = rendezvousPoint.RendezvousPoint(self.env, self) 
		yield new_rp.rp.request() # Request for parent node to acquire one end of the RP
		new_node.receiver_rp.append(new_rp) # RP assigned to new node
		self.owner_rp.append(new_rp)
		#print(self.owner_rp)
		new_node.my_membrane = self.my_membrane
		new_rp.membrane.append(self.my_membrane)
		'''

	def createFlow(self, new_flow): 
		#new_flow = flow.Flow(self.env, self, flow_specs) 
		yield new_flow.flow.request() # To be done at sender; Flow requested by the node
		self.cspace.append(new_flow) # Add flow to CSpace of the node
		#new_flow.membrane.append(self.my_membrane)
		#print(self.cspace[0])

	def createRendezvousPoint(self, new_rp):
		#new_rp = rendezvousPoint.RendezvousPoint(self.env, self)
		self.owner_rp.append(new_rp)
		#new_rp.membrane.append(self.my_membrane) # Move to wrap()
		yield new_rp.rp.request() # Request for parent node to acquire one end of the RP

	def createMembrane(self, new_membrane):
		#new_membrane = membrane.Membrane(self.env, self)
		self.my_membrane.append(new_membrane)
		yield new_membrane.membrane_rsc.request()
		#print(self.my_membrane)

	def addRPCap(self, rp, t):
		yield self.env.timeout(t)
		self.receiver_rp.append(rp)

	def sendCap(self, cap, rp, mem, t):
		yield self.env.timeout(t)
		#cap_type = cap.__class__.__name__
		#print(cap_type)
		#if cap_type == "RendezvousPoint":
		if mem is not None and mem not in cap.membrane and mem in self.my_membrane:
			yield self.env.process(mem.wrap(cap))
			print(cap)
			print(cap.membrane)
		# Check if needs to be wrapped by membrane of receiver
		for m in rp.membrane:
			if m not in cap.membrane:
				yield self.env.process(m.wrap(cap))
		rp.put(cap)
		print("Send {0} through {1} from {2} to {3}".format(cap, rp, self, rp.init_node))
	
	def recvCap(self, rp, mem, t):
		yield self.env.timeout(t)
		rp_recv = rp.get_output_conn()
		if rp in self.receiver_rp or rp in self.owner_rp:
			cap = yield rp_recv.get()
			print("Received {0} at {1}".format(cap, self))
			if mem in cap.membrane:
				yield self.env.process(mem.unwrap(cap))
			cap_type = cap.__class__.__name__
			print("Capability type: {0} ".format(cap_type))
			if cap_type == "RendezvousPoint":
				print(cap)
				print(cap.membrane)
				self.receiver_rp.append(cap)
				cap.attached_nodes.append(self)
			elif cap_type == "Flow":
				self.cspace.append(cap)
				cap.sender.append(self)
			elif cap_type == "Node":
				self.node_cap.append(cap)
				cap.node_owners.append(self)
	
	def revoke(self):
		# Remove all flows in cspace of the node
		for c in self.cspace:
			#c.callback()
			yield c.flow.release()
		self.cspace = [] 

	def delete(self, c):
		# Remove specific flow from cspace
		#c.callback()
		yield c.flow.release()
		self.cspace.remove(c)

	def reset(self, t):
		yield self.env.timeout(t)
		self.receiver_rp = []
		
		for my_rp in self.owner_rp:
			yield my_rp.rp.release(self)

		self.owner_rp = []

		self.env.process(self.revoke())

		#for l in reset_node.listener:
		#	self.env.process(l.callback())

		self.listener = []

		for m in self.membrane:
			if self in m.owner.node_cap:
				m.owner.node_cap.remove(self)
			# Else remove from derived nodes?
		
		for m in self.my_membrane:
			m.clear(t+1)
	
		print("Node Clean")
