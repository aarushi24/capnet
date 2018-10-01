import simpy
  
class Membrane:
        def __init__(self, owner):
		self.owner = owner
		self.scope = []
	
	def wrap(self, cap, receiver):
		self.scope.append(MembraneScope(cap, receiver))
		cap.membrane.append(self)

	def unwrap(self, cap, receiver):
		for i in range(len(self.scope)):
			if self.scope[i].receiver == receiver:
				break
		del self.scope[i]

class MembraneScope:
	def __init__(self, cap, receiver):
		self.cap = cap
		self.receiver = receiver
