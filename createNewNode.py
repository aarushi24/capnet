import simpy
import node

env = simpy.Environment()

#init events
n1 = node.Node(env)
print(n1)
n2 = node.Node(env)
env.process(n1.createMembrane())
env.process(n1.createNode(n2))
print(n2)

env.run()
