/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Normal

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- An affine étale object over a scheme is a finite disjoint union of open subschemes. -/
def HasFiniteOpenDecomposition (X : Scheme.{u}) : Prop :=
  ∀ (U : X.Etale) [IsAffine U.left],
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → Scheme.{u}) (e : U.left ≅ ∐ V)
      (j : ∀ i, V i ⟶ X),
      (∀ i, IsOpenImmersion (j i)) ∧ e.hom ≫ Sigma.desc j = U.hom

/-- A normal integral scheme with separably closed function field has finite affine étale open decompositions. -/
theorem hasFiniteOpenDecomposition_of_normalIntegral
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal) [IsSepClosed X.functionField] :
    HasFiniteOpenDecomposition X := sorry

end AlgebraicGeometry.Scheme.Etale
