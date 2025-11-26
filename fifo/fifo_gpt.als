// --------------------
// Signatures
// --------------------
sig Element {}
one sig e0, e1, e2, e3 extends Element {}

sig FIFO {
    var slot0: lone Element, // head
    var slot1: lone Element,
    var slot2: lone Element,
    var slot3: lone Element  // tail
}

one sig fifo extends FIFO {}

// --------------------
// Facts
// --------------------

// No duplicate elements
fact NoDuplicates {
    always all f: FIFO |
        all disj x, y: Element |
            ((x in f.slot0 + f.slot1 + f.slot2 + f.slot3) and
             (y in f.slot0 + f.slot1 + f.slot2 + f.slot3)) => x != y
}

// Initial FIFO empty
fact InitFIFO {
    no fifo.slot0
    no fifo.slot1
    no fifo.slot2
    no fifo.slot3
}

// --------------------
// Enqueue/Dequeue predicates
// --------------------

// Enqueue element into first empty slot (FIFO tail)
pred enqueue[f: FIFO, e: Element] {
    e not in f.slot0 + f.slot1 + f.slot2 + f.slot3
    no f.slot0 => f.slot0' = e else f.slot0' = f.slot0
    some f.slot0 and no f.slot1 => f.slot1' = e else f.slot1' = f.slot1
    some f.slot1 and no f.slot2 => f.slot2' = e else f.slot2' = f.slot2
    some f.slot2 and no f.slot3 => f.slot3' = e else f.slot3' = f.slot3
}

// Dequeue element from head (slot0)
pred dequeue[f: FIFO] {
    some f.slot0
    f.slot0' = f.slot1
    f.slot1' = f.slot2
    f.slot2' = f.slot3
    no f.slot3'
}

// --------------------
// FIFO temporal behavior
// --------------------
pred fifo_behavior {
    always (
        // Either enqueue an element if there is space
        (some e: Element | e not in fifo.slot0 + fifo.slot1 + fifo.slot2 + fifo.slot3 and enqueue[fifo, e])
        // Or dequeue if FIFO is non-empty
        or (some fifo.slot0 and dequeue[fifo])
    )
}

// --------------------
// Test: eventually full, then eventually empty
// --------------------
pred fifo_fill_then_empty {
    eventually (fifo.slot0 != none && fifo.slot1 != none &&
                fifo.slot2 != none && fifo.slot3 != none)
    eventually (no fifo.slot0 && no fifo.slot1 &&
                no fifo.slot2 && no fifo.slot3)
}

// --------------------
// Run command
// --------------------
run { fifo_behavior and fifo_fill_then_empty } for 4 Element, exactly 1 FIFO, 8 steps
