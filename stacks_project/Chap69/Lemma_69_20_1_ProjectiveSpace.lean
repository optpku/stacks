/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

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

/-- The functor of points of `ofScheme n S` is the Yoneda embedding of `P^n_S` over `S`. -/
theorem ofScheme_functorOfPoints (n : ℕ) (S : Scheme.{u}) :
    (ofScheme n S).functorOfPoints =
      yoneda.obj (Over.mk (AlgebraicGeometry.ProjectiveSpace.toBase n S)) :=
  sorry

/-- The algebraic space `ofScheme n S` is `ofOver` of the structure morphism of scheme-level
projective space. -/
theorem ofScheme_spec (n : ℕ) (S : Scheme.{u}) :
    ofScheme n S = ofOver (Over.mk (AlgebraicGeometry.ProjectiveSpace.toBase n S)) :=
  rfl

/-- Projective `n`-space over an algebraic space `Y` over `S`, as the fibre product
`Y ×_S P^n_S` of functors of points. -/
def ProjectiveSpace (n : ℕ) {S : Scheme.{u}} (Y : AlgebraicSpace S) : AlgebraicSpace S :=
  ofFunctor (Y.functorOfPoints ⨯ (ofScheme n S).functorOfPoints) sorry sorry sorry

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
