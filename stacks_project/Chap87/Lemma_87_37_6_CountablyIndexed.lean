/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_37_6_Affine

/-!
# Countably indexed affine formal algebraic spaces, functor of points

A functor of points `(Over S)ᵒᵖ ⥤ Type u` is a countably indexed affine
formal algebraic space when it is affine and admits an `ℕ`-indexed directed
affine thickening presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- An affine formal algebraic space is countably indexed when it admits an
`ℕ`-indexed directed affine thickening presentation. -/
class IsCountablyIndexedAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop
    extends IsAffine X where
  /-- There is an `ℕ`-indexed directed affine thickening presentation of
  `X`. -/
  exists_nat_colimit :
    ∃ D : ℕ ⥤ Over S, IsDirectedAffineThickeningColimit D X

namespace IsCountablyIndexedAffine

/-- Exhibit a countably indexed affine formal algebraic space by an
`ℕ`-indexed directed affine thickening colimit. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsAffine X]
    (D : ℕ ⥤ Over S) (h : IsDirectedAffineThickeningColimit D X) :
    IsCountablyIndexedAffine X :=
  sorry

/-- A countably indexed affine formal algebraic space unpacks as an affine
formal algebraic space together with an `ℕ`-indexed directed affine thickening
presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsCountablyIndexedAffine X] :
    IsAffine X ∧ ∃ D : ℕ ⥤ Over S, IsDirectedAffineThickeningColimit D X :=
  sorry

/-- An affine formal algebraic space is countably indexed if and only if it
admits an `ℕ`-indexed directed affine thickening presentation. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsCountablyIndexedAffine X ↔
      IsAffine X ∧ ∃ D : ℕ ⥤ Over S, IsDirectedAffineThickeningColimit D X :=
  sorry

/-- The representable functor of an affine scheme over `S` is countably
indexed, via the constant sequential system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsCountablyIndexedAffine (yoneda.obj U) :=
  sorry

end IsCountablyIndexedAffine

end AlgebraicGeometry.AffineFormalAlgebraicSpace
