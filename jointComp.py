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
#env.process(c_node.addRPCap(p_rp_public, 1))

# Step 1
c_mem = membrane.Membrane(env, c_node)
print("c_mem: {0}".format(c_mem))
c_rp = rendezvousPoint.RendezvousPoint(env, c_node)
print("c_rp: {0}".format(c_rp))

# Copy of RP to send to provider node 
env.process(c_node.sendCap(c_rp, p_rp_public, c_mem, 5))
env.process(p_node.recvCap(p_rp_public, p_mem, 5))

# Send new c_node through the c_rp sent 
c_node_2 = node.Node(env)
env.process(c_node.addNodeCap(c_node_2, 1))
env.process(c_node.sendCap(c_node_2, c_rp, c_mem, 10))
env.process(p_node.recvCap(c_rp, None, 10))

# TODO: How to implement "blocking receive on c_rp" (to allow provider to finish installing)

# Step 2
# Clean Node c_node_2
env.process(c_node_2.reset(15))

# Step 3
# install_service()

# Create rp for c_node_2 by p_node
c_rp_2 = rendezvousPoint.RendezvousPoint(env, c_node_2)
print("c_rp_2: {0}".format(c_rp_2))

# p_node sends rp over c_rp thus it is received membrane free
env.process(p_node.sendCap(c_rp_2, c_rp, c_mem, 20))
env.process(c_node.recvCap(c_rp, c_mem, 20))

# Step 4
# Clear membrane c_mem
env.process(c_mem.clear(25))

env.run()
