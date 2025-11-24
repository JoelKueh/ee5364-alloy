
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

// Predicate that updates registers based on the committed instruction.
pred UpdateRegs {
    all r: Register | (
        CommitEntry.ent.Output = r implies (
            r.ProducedBy' = CommitEntry.ent.Instr
        ) else (
            r.ProducedBy' = r.ProducedBy
        )
    )

    all r: Register | (
        IssueEntry.ent.Output' = r implies (
            r.Reserver' = IssueEntry.ent
        ) else (CommitEntry.ent.Output = r && r.Reserver = CommitEntry.ent) implies (
            no r.Reserver'
        ) else (
            r.Reserver' = r.Reserver
        )
    )
}

pred RobIsEmpty[e: RobEntry] {
    no e.Instr
    no e.Inputs
    no e.Deps
    no e.Output
    no e.InputsProducedBy
    e.State = RobFree
}

pred RobUpdateIssued[eIss: RobEntry] {
    // Instruction number is based on the current count.
    eIss.Instr' = CurrentInstr.i

    // Registers can have 1 to 2 inputs.
    (#eIss.Inputs' >= 1 && #eIss.Inputs' <= 2)

    // Handle value production times for all registers and in-flight instructions.
    all inst: InstrRecord | all e: RobEntry | all r: Register | e.Instr = inst implies (
        // Value can be read off of the CDB.
        (e.Output in eIss.Inputs' && not e in eIss.Deps') implies (
            inst in eIss.InputsProducedBy'
        ) else (
            not inst in eIss.InputsProducedBy'
        )
    ) else r.ProducedBy = inst implies (
        // If produced-by value is in a register, then take it.
        r in eIss.Inputs' implies (
            inst in eIss.InputsProducedBy'
        ) else (
            not inst in eIss.InputsProducedBy'
        )
    )

    all inst: InstrRecord | {
        not (some e: RobEntry | some r: Register | (e.Instr = inst || r.ProducedBy = inst)) implies (
            // If there is no RobEntry or Register associated with inst, then no dependence.
            not inst in eIss.InputsProducedBy'
        )
    }

    // Handle dependence for issued instruction.
    all e: RobEntry | all r: eIss.Inputs' | (
        (e = eIss) implies (
            // No self-dependence
            not (e in eIss.Deps')
        ) else not (e.Output = r) implies (
            // If output of previous is not input to current, then not dependence.
            not (e in eIss.Deps')
        ) else not (e.Output.Reserver = e) implies (
            // Non-transitive dependence graph.
            not (e in eIss.Deps')
        ) else (e.State = RobCommitReady) implies (
            // Value can be issued from the ROB.
            not (e in eIss.Deps')
        ) else (e = WritebackEntry.ent) implies (
            // Value can be issued from the CDB.
            not (e in eIss.Deps')
        ) else (
            // In all other cases, we have dependence.
            e in eIss.Deps'
        )
    )

    // Output assignment is implicit (either exists or doesn't, default behavior in alloy).

    // New entry state is RobReserved.
    eIss.State' = RobReserved
}

pred RobUpdateIssued_NoCDB[eIss: RobEntry] {
    // Instruction number is based on the current count.
    eIss.Instr' = CurrentInstr.i

    // Registers can have 1 to 2 inputs.
    (#eIss.Inputs' >= 1 && #eIss.Inputs' <= 2)

    // Handle value production times for all registers and in-flight instructions.
    all inst: InstrRecord | all r: Register | r.ProducedBy = inst implies (
        // If produced-by value is in a register, then take it.
        r in eIss.Inputs implies (
            inst in eIss.InputsProducedBy'
        ) else (
            not inst in eIss.InputsProducedBy'
        )
    )

    // If there is no register associated with inst, then no dependence.
    all inst: InstrRecord | {
        not (some r: Register | r.ProducedBy = inst) implies (
            not inst in eIss.InputsProducedBy'
        )
    }

    // Handle dependence for issued instruction.
    all e: RobEntry | all r: eIss.Inputs' | (
        (e = eIss) implies (
            // No self-dependence
            not (e in eIss.Deps')
        ) else not (e.Output = r) implies (
            // If output of previous is not input to current, then not dependence.
            not (e in eIss.Deps')
        ) else not (e.Output.Reserver = e) implies (
            // Non-transitive dependence graph.
            not (e in eIss.Deps')
        ) else (
            // In all other cases, we have dependence.
            e in eIss.Deps'
        )
    )

    // Output assignment is implicit (either exists or doesn't, default behavior in alloy).

    // New entry state is RobReserved.
    eIss.State' = RobReserved
}

pred RobUpdateCompleted[eComp: RobEntry] {
    // These fields do not change.
    eComp.Instr' = eComp.Instr
    eComp.Inputs' = eComp.Inputs
    no eComp.Deps'
    eComp.InputsProducedBy' = eComp.InputsProducedBy
    eComp.Output' = eComp.Output
    eComp.State' = RobCommitReady
}

pred RobUpdateCommitted[eCommit: RobEntry] {
    // Rob becomes empty.
    no eCommit.Instr'
    no eCommit.Inputs'
    no eCommit.Deps'
    no eCommit.InputsProducedBy'
    no eCommit.Output'
    eCommit.State' = RobFree
}

pred RobUpdatePassive[ePassive: RobEntry] {
    // These fields do not change.
    ePassive.Instr' = ePassive.Instr
	ePassive.Inputs' = ePassive.Inputs
    ePassive.Output' = ePassive.Output
    ePassive.State' = ePassive.State

    // Update dependenceis based on the current instruction in writeback.
    (WritebackEntry.ent in ePassive.Deps) implies (
        ePassive.Deps' = ePassive.Deps - WritebackEntry.ent &&
        ePassive.InputsProducedBy' = ePassive.InputsProducedBy + WritebackEntry.ent.Instr
    ) else (
        ePassive.Deps' = ePassive.Deps &&
        ePassive.InputsProducedBy' = ePassive.InputsProducedBy
    )
}

pred RobUpdatePassive_NoCDB[ePassive: RobEntry] {
    // These fields do not change.
    ePassive.Instr' = ePassive.Instr
	ePassive.Inputs' = ePassive.Inputs
    ePassive.Output' = ePassive.Output
    ePassive.State' = ePassive.State

    // Update dependenceis based on the current instruction in writeback.
    (some CommitEntry.ent && CommitEntry.ent in ePassive.Deps) implies (
        ePassive.Deps' = ePassive.Deps - CommitEntry.ent &&
        ePassive.InputsProducedBy' = ePassive.InputsProducedBy + CommitEntry.ent.Instr
    ) else (
        ePassive.Deps' = ePassive.Deps &&
        ePassive.InputsProducedBy' = ePassive.InputsProducedBy
    )
}

// Fact that updates Rob Entries.
pred UpdateRob {
    // Issued, Completed, and Committed entries have special update functions.
    some IssueEntry.ent => RobUpdateIssued[IssueEntry.ent]
    some WritebackEntry.ent => RobUpdateCompleted[WritebackEntry.ent]
    some CommitEntry.ent => RobUpdateCommitted[CommitEntry.ent]

    // All other registers just update dependencies and cycles to completion.
    all e: RobEntry | (
        not e = IssueEntry.ent && 
        not e = WritebackEntry.ent &&
        not e = CommitEntry.ent) implies (
        RobUpdatePassive[e]
    )
}

pred UpdateRob_NoCDB {
    // Issued, Completed, and Committed entries have special update functions.
    some IssueEntry.ent => RobUpdateIssued_NoCDB[IssueEntry.ent]
    some WritebackEntry.ent => RobUpdateCompleted[WritebackEntry.ent]
    some CommitEntry.ent => RobUpdateCommitted[CommitEntry.ent]

    // All other registers just update dependencies and cycles to completion.
    all e: RobEntry | (
        not e = IssueEntry.ent && 
        not e = WritebackEntry.ent &&
        not e = CommitEntry.ent) implies (
        RobUpdatePassive_NoCDB[e]
    )
}

// Predicate that updates rob entries based on the committed instruction.

// Predicates limiting what can issure, commit, and writeback in a cycle.
pred SingleIssue {
    // Issue to any free ROB entry.
    (some e: RobEntry | e.State = RobFree && IssueEntry.ent = e) ||
    (no IssueEntry.ent)
}

pred SingleWriteback {
    // Writeback any instruction.
    (some e: RobEntry | e.State = RobReserved && no e.Deps && WritebackEntry.ent = e) ||
    (no WritebackEntry.ent)
}

pred RandomCommit {
    // Commit any ready instruction.
    (some e: RobEntry | e.State = RobCommitReady && CommitEntry.ent = e) ||
    (no CommitEntry.ent)
}

pred OrderedCommit {
    // Commit the entry with the lowest InstrNum.
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
    always all e: RobEntry | all instr: e.InputsProducedBy | (
        not (e.Instr in prevs[instr])
    )
}

pred NoWAWHazard {
    always all r: Register | (
        no r.ProducedBy ||
        r.ProducedBy' = r.ProducedBy ||
        not (r.ProducedBy' in prevs[r.ProducedBy])
    )
}

// ERROR: Tomasulos without CDB or issue from ROB is vulnerable to WAR dependence!
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

//*<BEGIN_RUN_COMMANDS>*//

check NoWARHazard_WARVulnerable for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
check NoWARHazard_Complete for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
check NoWAWHazard_WAWVulnerable for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
check NoWAWHazard_Complete for exactly 4 RobEntry, exactly 4 Register, 6 InstrRecord, 6 steps, 4 Int

run {RobComplete} for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
run {RobWARVulnerable} for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int
run {RobWAWVulnerable} for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int

