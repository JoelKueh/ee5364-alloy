
// Nodes in the queue are ordered.
open util/ordering[FifoNode]

// Signiture defining and containing the state of the Fifo.
one sig Fifo { head: one FifoNode, nodes: set FifoNode }
sig FifoNode { var val: lone Int }

// Signiture defining an event that can take place in a timestep.
abstract sig Event {var status: EvStatus}
one sig EvEnq extends Event {var v: one Int}
one sig EvDeq extends Event {}

// Signiture defining states an event can be in.
abstract sig EvStatus {}
one sig EvActive, EvPassive extends EvStatus {}

// Initial conditions
fact {
	// All vallues in the FIFO are zero.
	all n: FifoNode | no n.val

	// All nodes in the FIFO belong to Fifo.Nodes
	all n: FifoNode | n in Fifo.nodes

	// Fifo has the head and tail of the ordered list of nodes.
	no Fifo.head.prev
}

// Predicates that can add or remove something from the Fifo on every timestep.
pred FifoEnq[v: Int] {
	Fifo.head.val' = v
	all n: FifoNode | some n.next => n.next.val' = n.val
}

pred FifoDeq {
	all n: FifoNode | (no n.val or no n.next.val) implies no n.val' else n.val' = n.val
}

// Predicate that makes sure that one event fires every cycle.
fact EventFires {
	always {
		EvEnq.status = EvActive || EvDeq.status = EvActive
		!(EvEnq.status = EvActive && EvDeq.status = EvActive)
		EvEnq.status = EvPassive => EvEnq.v = 0
	}
}

// Predicate that updates the state of the Fifo in the next timestep based on the current events.
fact FifoUpdate {
	always {
		EvEnq.status = EvActive => FifoEnq[EvEnq.v]
		EvDeq.status = EvActive => FifoDeq
	}
}

// Assertions made about the fifo.
pred Full {
    all n: Fifo.nodes | some n.val
}

pred Empty {
    all n: Fifo.nodes | no n.val
}

pred EventuallyFullThenEmpty {
	eventually {
        Full
        eventually {
            Empty
        }
    }
}

//*<BEGIN_RUN_COMMANDS>*//

run EventuallyFullThenEmpty for exactly 6 FifoNode, 12 steps, 5 Int
run {} for exactly 6 FifoNode, 8 steps, 5 Int
