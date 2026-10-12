/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap70.Remark_70_13_2

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 110.29.1: there exists a finite type morphism of algebraic spaces
`Y ⟶ X` with `Y` affine and `X` quasi-separated such that there does not exist
an immersion `Y ⟶ AffineSpace (ULift (Fin n)) X` over `X`. -/
@[stacks 088W]
theorem exists_finiteType_without_immersion_to_affineSpace :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsAffine Y ∧ FiniteType f ∧ IsAbsolutelyQuasiSeparated X ∧
        ¬ existsImmersionToAffineSpace f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
