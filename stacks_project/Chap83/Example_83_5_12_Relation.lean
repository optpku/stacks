module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import stacks_project.Chap83.Example_83_5_12_Spaces

/-!
# The s = 1, t = -1 pre-relation on the formal disk

This module packages the scheme pre-relation on `Y = Spec (PowerSeries k)`
whose projections are the identity and the automorphism `x ↦ -x`. The
involution quotient sheaf of Spaces, Example 65.14.1, is not locally
separated: see `not_isImmersion_diag_sheafOfPoints`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The pre-relation on `Y` with source `R = Y`, first projection `t = -1`, and
second projection `s = 1`. -/
def involutionPreRelation (k : Type u) [Field k] :
    Scheme.PreRelation (formalDisk k) :=
  Scheme.PreRelation.ofHom (prod.lift (formalDiskNeg k) (𝟙 (formalDisk k)))

/-- The defining map of `involutionPreRelation k` is the pair `(-1, 1)`. -/
theorem involutionPreRelation_hom (k : Type u) [Field k] :
    (involutionPreRelation k).hom =
      prod.lift (formalDiskNeg k) (𝟙 (formalDisk k)) := sorry

/-- The first projection of `involutionPreRelation k` is `-1`. -/
theorem involutionPreRelation_t (k : Type u) [Field k] :
    (involutionPreRelation k).t = formalDiskNeg k := sorry

/-- The second projection of `involutionPreRelation k` is the identity. -/
theorem involutionPreRelation_s (k : Type u) [Field k] :
    (involutionPreRelation k).s = 𝟙 (formalDisk k) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
