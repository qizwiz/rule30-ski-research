-- P2p.lean - Main library entry point for Rule 30 Prize proofs
-- Imports the complete proof chain explicitly so nothing important is orphaned.

-- Core definitions and prize theorem (via axioms)
import P2p.Prize3_Complete

-- SubcaseB component proofs (machine-checked)
import P2p.SubcaseBPeriod

-- Lifting lemma attempt (has axioms; blocks axiom-free path)
import P2p.LiftingLemma_LeftPermutive

-- X=2 witness infrastructure (1 sorry: twoSpike_center_complement)
import P2p.SpinePass
