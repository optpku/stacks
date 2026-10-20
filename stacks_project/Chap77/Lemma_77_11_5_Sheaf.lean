module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap77.Lemma_77_7_2_FpqcTopology
public import stacks_project.Chap77.«77_11_4_1_Functor»

/-!
# The fpqc sheaf property for the flat-in-dimensions functor on algebraic spaces

This module records fpqc descent for the functor detecting flatness in
dimensions at least a fixed natural number after base change to a scheme over
an algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

/-- The functor detecting flatness in dimensions at least `n` is an fpqc sheaf on
schemes over `Y`. -/
theorem flatInDimensionsFunctor_isSheaf_fpqc :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology Y) (flatInDimensionsFunctor f ℱ n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flattening
