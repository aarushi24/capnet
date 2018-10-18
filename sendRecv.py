import simpy
import node
import membrane 
import rendezvousPoint
import flow

env = simpy.Environment()

#init events

# Initial set up
p_node = node.Node(env)
print("p_node: {0}".format(p_node))
p_mem = membrane.Membrane(env, p_node)
print("p_mem: {0}".format(p_mem))
p_rp = rendezvousPoint.RendezvousPoint(env, p_node)
print("p_rp: {0}".format(p_rp))
# Create a "public" copy of the RP and wrap it in the membrane
p_rp_public = rendezvousPoint.RendezvousPoint(env, p_node)
print("p_rp_public: {0}".format(p_rp_public))
env.process(p_mem.wrap(p_rp_public))
#p_flow = flow.Flow(env, p_node, None)
#print(p_flow)

c_node = node.Node(env)
print("c_node: {0}".format(c_node))
c_mem = membrane.Membrane(env, c_node)
print("c_mem: {0}".format(c_mem))
c_rp = rendezvousPoint.RendezvousPoint(env, c_node)
print("c_rp: {0}".format(c_rp))

# Copy of RP to send to provider node 
env.process(c_node.sendCap(c_rp, p_rp_public, c_mem))
env.process(p_node.recvCap(p_rp_public, p_mem))

env.run()
