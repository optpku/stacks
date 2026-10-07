module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
import StacksCheckRecall

/-!
# Lemma 22.11.2

The Koszul change of handedness for differential graded modules is owned by
`ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite`.
-/

@[expose] public section

universe u v

/- Lemma 22.11.2 (0FQ0): for a cochain differential graded algebra `A`, sending a left
differential graded `A`-module to its Koszul-twisted right `A.opposite`-module is an equivalence
of categories. -/
@[stacks 0FQ0]
#check
  (@LeftDifferentialGradedModule.opEquivalence.{u, v} :
    {R : Type u} → [CommRing R] → (A : CochainDGAlgebra R) →
      LeftDifferentialGradedModule.{u, v} A ≌ DifferentialGradedModule.{u, v} A.opposite)
