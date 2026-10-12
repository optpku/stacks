/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Compact.KProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable {P : DifferentialGradedModule.{u, v} A}
variable (hP : DifferentialGradedModule.finiteKProjective A P)

/-!
# Remark 22.36.2 (09R1)

Finite graded projectivity is imposed after forgetting only the differential, so the graded
`A`-action is retained.  Together with the K-projective comparison condition, it gives a compact
object in the intrinsic derived category.
-/

@[stacks 09R1] #check
  (DifferentialGradedModule.Derived.FiniteKProjective.isCompactObject A hP :
    IsCompactObject ((DifferentialGradedModule.Derived.fromModules A).obj P))
#check @DifferentialGradedModule.finiteKProjective
#check @DifferentialGradedModule.finiteKProjective_iff
#check @DifferentialGradedModule.IsFiniteGradedProjective
#check @DifferentialGradedModule.Graded.IsFiniteProjective
#check @DifferentialGradedModule.Graded.IsFinitelyGenerated
#check @DifferentialGradedModule.Graded.isFiniteProjective_iff_projective_finitelyGenerated

/- Source-facing recall: finite generation of the underlying graded module is distinct from
compactness in the derived category; without the K-projective comparison condition, the latter is
not asserted here. -/
