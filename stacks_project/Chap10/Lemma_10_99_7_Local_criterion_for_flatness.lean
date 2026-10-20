module

public import ReasLib.RingTheory.Flatness.LocalCriterion.Tor
import StacksCheckRecall

/-!
# Local criterion for flatness

@stack 00MK

The reusable owner lives with the other `Tor₁` formulations of the local flatness criterion.
-/

@[expose] public section

/- Lemma 10.99.7 (Local criterion for flatness) (Tag 00MK): for a finite module over a local
homomorphism of local Noetherian rings, vanishing of `Tor₁` with the source residue field implies
flatness over the source. -/
@[stacks 00MK]
#check @Module.Flat.of_isZero_tor_one_residueField
