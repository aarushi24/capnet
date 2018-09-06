import simpy
import node

env = simpy.Environment()

#init events
na_rp0 = simpy.Store(env) # RP for node A
print(na_rp0)
na = node.Node(env, na_rp0)
#env.process(sendCap(env, na_rp0))

env.run()
