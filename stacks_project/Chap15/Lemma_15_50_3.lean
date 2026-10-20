module

public import ReasLib.RingTheory.FormalFiber.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.3

@stack 07PP
-/

@[expose] public section

/-! # Lemma 15.50.3: quasi-finite transfer of geometrically regular formal fibers -/

/- Lemma 15.50.3 (1), tag `07PP`: geometric regularity transfers to a corresponding formal
fiber under a quasi-finite map. -/
@[stacks 07PP "(1), quasi-finite transfer of a formal fiber"]
#check @IsGRing.QuasiFiniteAt.formalFiber

/- Lemma 15.50.3 (2), tag `07PP`: geometric regularity of all formal fibers transfers at a
quasi-finite target prime. -/
@[stacks 07PP "(2), quasi-finite transfer of formal fibers"]
#check @IsGRing.QuasiFiniteAt.formalFibers

/- Lemma 15.50.3 (3), tag `07PP`: quasi-finite finite-type extensions of G-rings are G-rings. -/
@[stacks 07PP "(3), quasi-finite extension of a G-ring"]
#check @IsGRing.of_quasiFinite
