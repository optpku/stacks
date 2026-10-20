/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small

/-!
# Presentations of algebraic stacks

A presentation of an algebraic stack `X` over `S` is a smooth groupoid in algebraic
spaces over `S` together with an equivalence from its quotient stack to `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A presentation of an algebraic stack `X` over `S` consists of a smooth groupoid
`(U, R, s, t, c)` in algebraic spaces over `S` and an equivalence `f : [U / R] ⟶ X`. -/
structure Presentation {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] where
  /-- The presenting groupoid in algebraic spaces over `S`. -/
  groupoid : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S)))
  /-- The presenting groupoid is smooth. -/
  isSmooth : GroupoidAlgebraicSpace.Smooth groupoid
  /-- The equivalence `f : [U / R] ⟶ X`. -/
  hom : GroupoidAlgebraicSpace.SmallQuotient.quotientStack groupoid ⟶ X
  /-- `hom` is an equivalence of categories fibred in groupoids over `Over S`. -/
  isEquivalence : (FiberedCategoryOver.Groupoids.toBasedFunctor hom).IsEquivalence

namespace Presentation

/-- Build a presentation from a smooth groupoid over `S` and an equivalence from its
quotient stack. -/
def of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
    [GroupoidAlgebraicSpace.Smooth G] (f : GroupoidAlgebraicSpace.SmallQuotient.quotientStack G ⟶ X)
    (hf : (FiberedCategoryOver.Groupoids.toBasedFunctor f).IsEquivalence) :
    Presentation X where
  groupoid := G
  isSmooth := inferInstance
  hom := f
  isEquivalence := hf

/-- The groupoid of `of G f hf` is the supplied groupoid. -/
@[simp]
theorem of_groupoid {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
    [GroupoidAlgebraicSpace.Smooth G] (f : GroupoidAlgebraicSpace.SmallQuotient.quotientStack G ⟶ X)
    (hf : (FiberedCategoryOver.Groupoids.toBasedFunctor f).IsEquivalence) :
    (of G f hf).groupoid = G := sorry

/-- The equivalence of `of G f hf` is the supplied `1`-morphism. -/
@[simp]
theorem of_hom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
    [GroupoidAlgebraicSpace.Smooth G] (f : GroupoidAlgebraicSpace.SmallQuotient.quotientStack G ⟶ X)
    (hf : (FiberedCategoryOver.Groupoids.toBasedFunctor f).IsEquivalence) :
    (of G f hf).hom = f := sorry

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- A presentation consists of a smooth groupoid over `S` and an equivalence from its
quotient stack. -/
theorem spec (P : Presentation X) :
    GroupoidAlgebraicSpace.Smooth P.groupoid ∧
      (FiberedCategoryOver.Groupoids.toBasedFunctor P.hom).IsEquivalence :=
  sorry

/-- The presenting groupoid of a presentation is smooth. -/
theorem smooth (P : Presentation X) : GroupoidAlgebraicSpace.Smooth P.groupoid :=
  sorry

/-- The `1`-morphism of a presentation is an equivalence over `Over S`. -/
theorem hom_isEquivalence (P : Presentation X) :
    (FiberedCategoryOver.Groupoids.toBasedFunctor P.hom).IsEquivalence :=
  sorry

end Presentation

end AlgebraicGeometry.AlgebraicStack
