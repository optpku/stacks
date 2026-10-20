/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Projective space as an algebraic space

Projective `n`-space over an algebraic space `Y` over a scheme `S` is the fibre product
`Y ×_S P^n_S`, realized as the binary product of functors of points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Projective `n`-space over a scheme `S`, viewed as an algebraic space over `S`. -/
def ofScheme (n : ℕ) (S : Scheme.{u}) : AlgebraicSpace S :=
  ofOver (Over.mk (AlgebraicGeometry.ProjectiveSpace.toBase n S))

namespace ProjectiveSpace

/-- The product of the functors of points of an algebraic space and projective space
satisfies fppf descent. -/
theorem product_isSheaf (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints) :=
  sorry

/-- The product of an algebraic space and represented projective space has representable
diagonal. -/
theorem product_representableDiagonal (n : ℕ) {S : Scheme.{u}}
    (Y : AlgebraicSpace S) :
    yoneda.relativelyRepresentable
      (Limits.diag (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints)) :=
  sorry

/-- The product of an algebraic space and represented projective space admits a
representable étale locally-surjective scheme atlas. -/
theorem product_atlas (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    ∃ (U : Over S)
      (p : yoneda.obj U ⟶ (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints)),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  sorry

end ProjectiveSpace

/-- Projective `n`-space over an algebraic space `Y` over `S`, as the fibre product
`Y ×_S P^n_S` of functors of points. -/
def ProjectiveSpace (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) : AlgebraicSpace S :=
  ofFunctor (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints)
    (ProjectiveSpace.product_isSheaf n Y)
    (ProjectiveSpace.product_representableDiagonal n Y) (ProjectiveSpace.product_atlas n Y)

namespace ProjectiveSpace

/-- The functor of points of `ProjectiveSpace n Y` is the binary product of the functors of
points of `Y` and of `P^n_S`. -/
theorem functorOfPoints_eq (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    (ProjectiveSpace n Y).functorOfPoints =
      (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints) :=
  rfl

/-- The structure morphism `π : P^n_Y ⟶ Y`. -/
def toBase (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    ProjectiveSpace n Y ⟶ Y :=
  (prod.fst :
    (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints) ⟶ Y.functorOfPoints)

/-- The projection `P^n_Y ⟶ P^n_S` used to pull back `𝒪(1)`. -/
def toOfScheme (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    ProjectiveSpace n Y ⟶ ofScheme n S :=
  (prod.snd :
    (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints) ⟶
      (ofScheme n S).functorOfPoints)


end ProjectiveSpace

end AlgebraicGeometry.AlgebraicSpace
