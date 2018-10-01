import simpy
import node

env = simpy.Environment()

#init events
p_node = node.Node(env)
print(p_node)
c_node = node.Node(env)
print(c_node)
env.process(p_node.createMembrane())
env.process(c_node.createMembrane())
env.process(p_node.createRendezvousPoint())
env.process(c_node.createRendezvousPoint())
env.process(c_node.sendCap(p_node))
env.process(p_node.recvCap())

env.run()
