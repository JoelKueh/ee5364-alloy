// The step list needs to be ordered.
open util/ordering[InstrRecord]

// Signiture defining an ROB used in a Tomasulo's machine.
one sig Rob { Entries: set RobEntry }
sig RobEntry {
    var Instr: lone InstrRecord,    // The instruction.
    var Inputs: set Register,       // List of registers from inputs.
    var Deps: set RobEntry,         // List of non-ready input dependencies.
    var InputsProducedBy: set InstrRecord,
    var Output: lone Register,      // Output register.
    var State: one RobStatus        // Status of the entry.
}

// Signiture defining the different states an ROB entry can be in.
abstract sig RobStatus {}
one sig RobFree, RobReserved, RobCommitReady extends RobStatus {}

// Signiture defining the structure of the register file.
one sig Rfile { Regs: set Register }
sig Register {
    var ProducedBy: lone InstrRecord,   // Instruction that last set this register.
    var Reserver: lone RobEntry         // Entry that last reserved this register.
}

// Signiture tracking the instruction that will be issued next.
sig InstrRecord {}
one sig CurrentInstr { var i: one InstrRecord }

// Signiture tracking rob entries that will be updated this cycle.
one sig IssueEntry { var ent: lone RobEntry }
one sig WritebackEntry { var ent: lone RobEntry }
one sig CommitEntry { var ent: lone RobEntry }

// Initial conditions
fact {
    // All RobEntries start out free, belonging to the Rob
    all e: RobEntry | RobIsEmpty[e]
    all e: RobEntry | e in Rob.Entries

    // All registers start out with no reserver produced in 0, belonging to the Rfile.
    all r: Register | no r.ProducedBy && no r.Reserver
    all r: Register | r in Rfile.Regs

    // Current instruciton starts out pointing to the first in the record.
    no CurrentInstr.i.prev
}

// Always switch to the next instruction.
fact {
    always {
        (no CurrentInstr.i.next) implies (
            CurrentInstr.i' = CurrentInstr.i
        ) else (
            CurrentInstr.i' = CurrentInstr.i.next
        )
    }
}

// Predicate that updates registers based on the issued or committed instruction.
pred UpdateRegs {
    all r: Register | {
        // 1. Handle Rename Table (Reserver)
        // If issuing, this entry becomes the reserver.
        // If committing AND this entry is still the reserver, free it.
        // (If a later instruction has already reserved it, do not clear).
        some IssueEntry.ent and IssueEntry.ent.Output = r implies (
            r.Reserver' = IssueEntry.ent
        ) else (some CommitEntry.ent and CommitEntry.ent.Output = r and r.Reserver = CommitEntry.ent) implies (
            no r.Reserver'
        ) else (
            r.Reserver' = r.Reserver
        )

        // 2. Handle Architectural File (ProducedBy)
        // Only updates on commit.
        some CommitEntry.ent and CommitEntry.ent.Output = r implies (
            r.ProducedBy' = CommitEntry.ent.Instr
        ) else (
            r.ProducedBy' = r.ProducedBy
        )
    }
}

pred RobIsEmpty[e: RobEntry] {
    no e.Instr
    no e.Inputs
    no e.Deps
    no e.Output
    no e.InputsProducedBy
    e.State = RobFree
}

// CORRECT: Snapshot dependencies at Issue.
pred RobUpdateIssued[eIss: RobEntry] {
    eIss.Instr' = CurrentInstr.i
    (#eIss.Inputs' >= 1 && #eIss.Inputs' <= 2)
    one r: Register | eIss.Output' = r

    // Snapshot dependencies: Look at Reservers NOW. 
    // Optimization: If Reserver is on CDB (WritebackEntry) now, don't add dep.
    eIss.Deps' = { dep: RobEntry | 
        some r: eIss.Inputs' | 
        r.Reserver = dep and dep != WritebackEntry.ent 
    }

    eIss.InputsProducedBy' = { i: InstrRecord |
        some r: eIss.Inputs' |
        (no r.Reserver and r.ProducedBy = i) or
        (some r.Reserver and r.Reserver.Instr = i)
    }

    eIss.State' = RobReserved
}

// FLAWED START: The logic here is mostly fine, but it sets up the flawed passive state.
pred RobUpdateIssued_NoCDB[eIss: RobEntry] {
    eIss.Instr' = CurrentInstr.i
    (#eIss.Inputs' >= 1 && #eIss.Inputs' <= 2)
    one r: Register | eIss.Output' = r

    // No CDB optimization
    eIss.Deps' = { dep: RobEntry | 
        some r: eIss.Inputs' | 
        r.Reserver = dep 
    }

    eIss.InputsProducedBy' = { i: InstrRecord |
        some r: eIss.Inputs' |
        (no r.Reserver and r.ProducedBy = i) or
        (some r.Reserver and r.Reserver.Instr = i)
    }

    eIss.State' = RobReserved
}

pred RobUpdateCompleted[eComp: RobEntry] {
    eComp.Instr' = eComp.Instr
    eComp.Inputs' = eComp.Inputs
    no eComp.Deps'
    eComp.InputsProducedBy' = eComp.InputsProducedBy
    eComp.Output' = eComp.Output
    eComp.State' = RobCommitReady
}

pred RobUpdateCommitted[eCommit: RobEntry] {
    no eCommit.Instr'
    no eCommit.Inputs'
    no eCommit.Deps'
    no eCommit.InputsProducedBy'
    no eCommit.Output'
    eCommit.State' = RobFree
}

// CORRECT: Passive updates only resolve existing deps, never add new ones.
pred RobUpdatePassive[ePassive: RobEntry] {
    ePassive.Instr' = ePassive.Instr
    ePassive.Inputs' = ePassive.Inputs
    ePassive.Output' = ePassive.Output
    ePassive.State' = ePassive.State
    
    // Correct Logic: Only remove dependencies that have broadcasted.
    // Never look at the Register File again.
    ePassive.Deps' = ePassive.Deps - WritebackEntry.ent
    
    // History does not change
    ePassive.InputsProducedBy' = ePassive.InputsProducedBy 
}

// FLAWED: This predicate creates the WAR vulnerability.
pred RobUpdatePassive_NoCDB[ePassive: RobEntry] {
    ePassive.Instr' = ePassive.Instr
    ePassive.Inputs' = ePassive.Inputs
    ePassive.Output' = ePassive.Output
    ePassive.State' = ePassive.State
    
    // WAR FLAW: Re-evaluate dependencies based on CURRENT register state.
    // If a younger instruction issues and reserves the register we are waiting on,
    // we mistakenly update our dependency to wait for that YOUNGER instruction.
    ePassive.Deps' = { dep: RobEntry | 
        some r: ePassive.Inputs | 
        r.Reserver = dep 
    }
    
    // Update the record to reflect this logical error so the assertion catches it.
    ePassive.InputsProducedBy' = { i: InstrRecord |
        some r: ePassive.Inputs |
        (no r.Reserver and r.ProducedBy = i) or
        (some r.Reserver and r.Reserver.Instr = i)
    }
}

// Fact that updates Rob Entries.
pred UpdateRob {
    some IssueEntry.ent => RobUpdateIssued[IssueEntry.ent]
    some WritebackEntry.ent => RobUpdateCompleted[WritebackEntry.ent]
    some CommitEntry.ent => RobUpdateCommitted[CommitEntry.ent]

    all e: RobEntry | (
        not e = IssueEntry.ent && 
        not e = WritebackEntry.ent &&
        not e = CommitEntry.ent) implies (
        RobUpdatePassive[e]
    )
}

pred UpdateRob_NoCDB {
    some IssueEntry.ent => RobUpdateIssued_NoCDB[IssueEntry.ent]
    some WritebackEntry.ent => RobUpdateCompleted[WritebackEntry.ent]
    some CommitEntry.ent => RobUpdateCommitted[CommitEntry.ent]

    all e: RobEntry | (
        not e = IssueEntry.ent && 
        not e = WritebackEntry.ent &&
        not e = CommitEntry.ent) implies (
        RobUpdatePassive_NoCDB[e]
    )
}

// Predicates limiting what can issure, commit, and writeback in a cycle.
pred SingleIssue {
    (some e: RobEntry | e.State = RobFree && IssueEntry.ent = e) ||
    (no IssueEntry.ent)
}

pred SingleWriteback {
    (some e: RobEntry | e.State = RobReserved && no e.Deps && WritebackEntry.ent = e) ||
    (no WritebackEntry.ent)
}

pred RandomCommit {
    (some e: RobEntry | e.State = RobCommitReady && CommitEntry.ent = e) ||
    (no CommitEntry.ent)
}

pred OrderedCommit {
    (some e1: RobEntry | all e2: RobEntry | e1.State = RobCommitReady &&
        (not e2.State = RobFree => e1 = e2 || e1.Instr in prevs[e2.Instr]) &&
        CommitEntry.ent = e1) ||
    (no CommitEntry.ent)
}

pred RobRandomCommit {
    always {
        SingleIssue
        SingleWriteback
        RandomCommit
    }
}

pred RobOrderedCommit {
    always {
        SingleIssue
        SingleWriteback
        OrderedCommit
    }
}

pred NoWARHazard {
    always all e: RobEntry |
    all instr: e.InputsProducedBy | (
        not (e.Instr in prevs[instr])
    )
}

pred NoWAWHazard {
    always all r: Register |
    (
        no r.ProducedBy ||
        r.ProducedBy' = r.ProducedBy ||
        not (r.ProducedBy' in prevs[r.ProducedBy])
    )
}

// ERROR: This configuration will now generate a counterexample.
pred RobWARVulnerable {
    always {
        RobRandomCommit
        UpdateRegs
        UpdateRob_NoCDB
    }
}

// ERROR: RandomCommit is vulnerable to WAW depencence!
pred RobWAWVulnerable {
    always {
        RobRandomCommit
        UpdateRegs
        UpdateRob
    }
}

pred RobComplete {
    always {
        RobOrderedCommit
        UpdateRegs
        UpdateRob
    }
}

// Assertions for WAR and WAW depencences.
assert NoWARHazard_WARVulnerable {
    RobWARVulnerable => NoWARHazard
}

assert NoWARHazard_Complete {
    RobComplete => NoWARHazard
}

assert NoWAWHazard_WAWVulnerable {
    RobWAWVulnerable => NoWAWHazard
}

assert NoWAWHazard_Complete {
    RobComplete => NoWAWHazard
}

pred SomeDependency {
	eventually {
		some e: RobEntry | some e.Inputs and some e.Output and some e.Deps and e not in e.Deps
	}
}

//*<BEGIN_RUN_COMMANDS>*//

check NoWARHazard_WARVulnerable for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
check NoWARHazard_Complete for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
check NoWAWHazard_WAWVulnerable for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
check NoWAWHazard_Complete for exactly 4 RobEntry, exactly 4 Register, 6 InstrRecord, 6 steps, 4 Int

run {SomeDependency} for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
run {RobComplete} for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int

