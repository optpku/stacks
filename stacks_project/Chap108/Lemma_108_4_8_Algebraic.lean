/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import stacks_project.Chap108.Lemma_108_4_1_Diagonal

/-!
# Algebraic stacks in the Hom-universe of `CohStack.toGroupoids`

An algebraic stack in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is a stack in groupoids whose diagonal is representable by algebraic spaces and
which admits a smooth surjective scheme atlas, matching Definition 94.12.1 at the
Hom-universe of `CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- The canonical 1-morphism from a CohStack-sized groupoid fibration to the
universe-lifted slice of the identity morphism of `S`. -/
def toIdentitySlice {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :
    X ⟶ Classifying.slice (Over.mk (𝟙 S)) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { obj := fun x ↦
        ULiftHom.objUp.{u + 1, u + 1}
          (Over.mk (Over.homMk (X.p.obj x).hom sorry))
      map := fun f ↦ ⟨Over.homMk (X.p.map f) sorry⟩
      map_id := sorry
      map_comp := sorry
      w := sorry }

/-- The underlying functor of `toIdentitySlice` lies strictly over `Over S`. -/
theorem toIdentitySlice_p {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :
    FiberedCategoryOver.Groupoids.toFunctor (toIdentitySlice X) ⋙
        Classifying.sliceProjection (Over.mk (𝟙 S)) =
      X.p :=
  sorry

/-- The object-level diagonal of a CohStack-sized groupoid fibration, obtained as
the relative 2-diagonal of `toIdentitySlice`. -/
noncomputable def diagonal {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :
    X ⟶ CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1}
      (toIdentitySlice X) (toIdentitySlice X) :=
  Hom.diagonal (toIdentitySlice X)

/-- The object-level diagonal is the relative 2-diagonal of `toIdentitySlice`. -/
theorem diagonal_eq {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :
    diagonal X = Hom.diagonal (toIdentitySlice X) :=
  sorry

/-- An algebraic stack over a scheme `S`, in the Hom-universe of
`CohStack.toGroupoids`, is a category fibred in groupoids over `(Sch/S)_fppf`
that is a stack in groupoids, whose diagonal is representable by algebraic
spaces, and that admits a scheme atlas which is surjective and smooth. -/
class AlgebraicStack {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) : Prop where
  /-- The category is a stack in groupoids over the big fppf site of `S`. -/
  isStack : IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p
  /-- The diagonal `Δ : X ⟶ X × X` is representable by algebraic spaces. -/
  representableDiagonal :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal X)
  /-- There is a scheme `U` over `S` and a surjective smooth 1-morphism
  `Classifying.slice U ⟶ X`. -/
  existsSmoothSurjectiveAtlas :
    ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
      Classifying.Smooth p ∧ Classifying.Surjective p

namespace AlgebraicStack

/-- The canonical slice fibration of a scheme over `S` is an algebraic stack. -/
instance slice {S : Scheme.{u}} (U : Over S) :
    AlgebraicStack (Classifying.slice U) :=
  sorry

/-- The groupoid fibration of an algebraic space is an algebraic stack. -/
instance ofAlgebraicSpace {S : Scheme.{u}} (F : AlgebraicSpace S) :
    AlgebraicStack (Classifying.toGroupoids F) :=
  sorry

/-- The three defining clauses of an algebraic stack in the Hom-universe of
`CohStack.toGroupoids`. -/
theorem spec {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p ∧
      Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal X) ∧
        ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
          Classifying.Smooth p ∧ Classifying.Surjective p :=
  sorry

/-- Being an algebraic stack is equivalent to the three defining clauses: stack
in groupoids, diagonal representable by algebraic spaces, and a surjective
smooth scheme atlas. -/
theorem iff {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :
    AlgebraicStack X ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p ∧
        Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal X) ∧
          ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
            Classifying.Smooth p ∧ Classifying.Surjective p :=
  sorry

end AlgebraicStack

end AlgebraicGeometry.AlgebraicSpace.CohStack
