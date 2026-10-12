/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.PointSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Nonexistence of quasi-compact dense open subschemes

The infinite-product algebraic-space example is quasi-compact and quasi-separated but has no
quasi-compact dense open subscheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space contains a quasi-compact dense open subscheme for a given topology on its
point space. -/
def HasQuasiCompactDenseOpenSubscheme {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∃ (τ : TopologicalSpace (Points X)),
    IsPointsTopology X τ ∧
      ∃ (T : Over S) (ι : ofOver T ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion)).presheaf ι ∧
          IsQuasiCompact (ofOver T) ∧
          @Dense (Points X) τ (Set.range (Points.map ι))

namespace InfiniteProduct

/-- The infinite-product quotient gives a quasi-compact and quasi-separated algebraic space with
no quasi-compact dense open subscheme. -/
theorem exists_no_quasiCompact_dense_open :
    ∃ (k : Type u) (_ : Field k) (X : AlgebraicSpace (Spec (CommRingCat.of k))),
      IsQuasiCompact X ∧ IsQuasiSeparated X ∧
        ¬ HasQuasiCompactDenseOpenSubscheme X :=
  sorry

end InfiniteProduct

end AlgebraicGeometry.AlgebraicSpace
