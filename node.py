import simpy

class Node:
	def __init__(self, env, rp0):
		self.env = env
		self.rp0 = rp0
		self.cap = self.sendCap() # testing sending capability
		
	def createNewNode(self):
		newNode = Node(self.env)
		return newNode
	
	def createRendezvousPoint(self):
		new_rp = simpy.Store(self.env)
		return new_rp	

	def sendCap(self):
        	#yield self.env.timeout(1)
        	self.rp0.put('test')
        	self.env.process(self.recvCap())

	def recvCap(self):
        	msg = yield self.rp0.get()
        	print(msg)
