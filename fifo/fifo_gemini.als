module fifo_int

// ---------------------------------------------------------
// Configuration
// ---------------------------------------------------------

one sig FIFO {
    // The content is now a sequence of Integers
    var content: seq Int
}

// ---------------------------------------------------------
// Operations
// ---------------------------------------------------------

pred init {
    no FIFO.content
}

pred enqueue[i: Int] {
    // Guard: Check against our explicit 'capacity' function
    // (Using implicit integer arithmetic)
    #FIFO.content < capacity

    // Effect: Add the integer to the sequence
    FIFO.content' = FIFO.content.add[i]
}

pred dequeue {
    // Guard: content must have at least one item
    some FIFO.content

    // Effect: Remove the head
    FIFO.content' = FIFO.content.rest
}

// ---------------------------------------------------------
// System Trace
// ---------------------------------------------------------

fact SystemTrace {
    init
    always {
        // Step choice: Enqueue some integer OR Dequeue
        (some i: Int | enqueue[i])
        or
        dequeue
    }
}

// ---------------------------------------------------------
// Verification
// ---------------------------------------------------------

pred fill_and_then_empty {
    eventually {
        // Check if the sequence length equals our defined capacity
        #FIFO.content = capacity

        // Then check if it later becomes empty
        eventually {
            no FIFO.content
        }
    }
}

//*<BEGIN_RUN_COMMANDS>*//

fun capacity: Int { 5 }
run fill_and_then_empty for 12 steps, 4 Int
