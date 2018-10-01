import simpy
import node

env = simpy.Environment()

#init events
n1 = node.Node(env)
print(n1)
env.process(n1.createMembrane())
env.process(n1.createRendezvousPoint())
env.process(n1.createFlow(None))

env.run()
