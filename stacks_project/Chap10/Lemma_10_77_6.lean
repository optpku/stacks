module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Lift
import StacksCheckRecall

/-!
# Lemma 10.77.6 recall

The reusable owner is `Module.Projective.exists_finite_lift_of_isLocallyNilpotent`.  It separates
the finite projective lifting statement from the chapter-specific finite-free projector
construction used to prove it.

@stack 0D47
-/

@[expose] public section

/- Lemma 10.77.6 (0D47): a finite projective `R ⧸ I`-module lifts across a locally nilpotent
ideal of a commutative ring to a finite projective `R`-module. -/
@[stacks 0D47] #check @Module.Projective.exists_finite_lift_of_isLocallyNilpotent
