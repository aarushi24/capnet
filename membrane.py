import simpy
  
class Membrane:
        def __init__(self, env, owner):
		self.env = env
		self.owner = owner
		self.scope = []
		self.membrane_rsc = simpy.Resource(self.env, capacity=1)
	
	def wrap(self, cap, receiver):
		self.scope.append(MembraneScope(cap, receiver))
		cap.membrane.append(self)

	def unwrap(self, cap, receiver):
		i = -1
		for i in range(len(self.scope)):
			if self.scope[i].receiver == receiver:
				break
		if -1 < i < len(self.scope):
			del self.scope[i]

class MembraneScope:
	def __init__(self, cap, receiver):
		self.cap = cap
		self.receiver = receiver
