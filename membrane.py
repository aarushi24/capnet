import simpy
  
class Membrane:
        def __init__(self, env, owner):
		self.env = env
		self.owner = owner
		self.wrapped_cap = []
		self.membrane_rsc = simpy.Resource(self.env, capacity=1)
		self.env.process(self.owner.createMembrane(self))
	
	def wrap(self, cap):
		yield self.env.timeout(1)
		self.wrapped_cap.append(cap)
		cap.membrane.append(self)
		#print(cap.membrane)

	def unwrap(self, cap):
		yield self.env.timeout(1)
		self.wrapped_cap.remove(cap)
		cap.membrane.remove(self)

	def clear(self, t):
		yield self.env.timeout(t)
		for cap in self.wrapped_cap:
			cap_type = cap.__class__.__name__
			if cap_type == "RendezvousPoint":
				for n in cap.attached_nodes:
					n.receiver_rp.remove(cap)
			elif cap_type == "Flow":
				for n in cap.sender:
					n.cspace.remove(cap)
			elif cap_type == "Node":
				for n in cap.node_owners:
					if cap in n.node_cap:
						n.node_cap.remove(cap)
					cap.node_owners = []
			cap.membrane = []
