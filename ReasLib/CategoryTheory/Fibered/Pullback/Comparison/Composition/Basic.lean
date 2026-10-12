/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.AssocLeftProjection.Equivalence

/-!
# Composition comparison for pullback of fibred categories

This leaf lifts categorical-pullback reassociation to explicit equivalence data over the
leftmost base. The quasi-inverse is universe-polymorphic; its fixed-bicategory packaging is
available on the stable common-universe layer.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits
open scoped CategoryTheory.BasedFunctor CategoryTheory.Bicategory

namespace CategoryTheory.FiberedCategoryOver.Pullback.Comp

universe uC uD uE uS vC vD vE vS

variable {C : Type uC} {D : Type uD} {E : Type uE}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
variable (u : C ⥤ D) (v : D ⥤ E)
variable (X : FiberedCategoryOver.{uE, vE, uS, vS} E)

/-- Forward reassociation commutes strictly with the projection to the leftmost base. -/
theorem forward.compProjection :
    CategoricalPullback.LeftProjection.forward u v X.p ⋙
        (FiberedCategoryOver.pullback (u ⋙ v) X).p =
      (FiberedCategoryOver.pullback u
        (FiberedCategoryOver.pullback v X)).p := sorry

/-- The based forward comparison from iterated pullback to pullback along the composite. -/
def forwardBased :
    (FiberedCategoryOver.pullback u
        (FiberedCategoryOver.pullback v X)).toBasedCategory ⥤ᵇ
      (FiberedCategoryOver.pullback (u ⋙ v) X).toBasedCategory :=
  BasedFunctor.ofFunctor
    (CategoricalPullback.LeftProjection.forward u v X.p)
    (forward.compProjection u v X)

/-- Inverse reassociation commutes strictly with the projection to the leftmost base. -/
theorem inverse.compProjection :
    CategoricalPullback.LeftProjection.inverse u v X.p ⋙
        (FiberedCategoryOver.pullback u
          (FiberedCategoryOver.pullback v X)).p =
      (FiberedCategoryOver.pullback (u ⋙ v) X).p := sorry

/-- The based inverse comparison from pullback along the composite to iterated pullback. -/
def inverseBased :
    (FiberedCategoryOver.pullback (u ⋙ v) X).toBasedCategory ⥤ᵇ
      (FiberedCategoryOver.pullback u
        (FiberedCategoryOver.pullback v X)).toBasedCategory :=
  BasedFunctor.ofFunctor
    (CategoricalPullback.LeftProjection.inverse u v X.p)
    (inverse.compProjection u v X)

/-- The categorical reassociation unit is vertical over the leftmost base. -/
theorem unit.isHomLift
    (x : (FiberedCategoryOver.pullback u
      (FiberedCategoryOver.pullback v X)).total) :
    (FiberedCategoryOver.pullback u
        (FiberedCategoryOver.pullback v X)).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.pullback u
        (FiberedCategoryOver.pullback v X)).p.obj x))
      ((CategoricalPullback.LeftProjection.equivalence u v X.p).unitIso.hom.app x) := sorry

/-- The categorical reassociation unit as a based natural isomorphism. -/
def unitIso :
    𝟙 (FiberedCategoryOver.pullback u
        (FiberedCategoryOver.pullback v X)).toBasedCategory ≅
      forwardBased u v X ⋙ inverseBased u v X :=
  BasedNatIso.mkNatIso
    (CategoricalPullback.LeftProjection.equivalence u v X.p).unitIso
    (unit.isHomLift u v X)

/-- The categorical reassociation counit is vertical over the leftmost base. -/
theorem counit.isHomLift
    (x : (FiberedCategoryOver.pullback (u ⋙ v) X).total) :
    (FiberedCategoryOver.pullback (u ⋙ v) X).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.pullback (u ⋙ v) X).p.obj x))
      ((CategoricalPullback.LeftProjection.equivalence u v X.p).counitIso.hom.app x) := sorry

/-- The categorical reassociation counit as a based natural isomorphism. -/
def counitIso :
    inverseBased u v X ⋙ forwardBased u v X ≅
      𝟙 (FiberedCategoryOver.pullback (u ⋙ v) X).toBasedCategory :=
  BasedNatIso.mkNatIso
    (CategoricalPullback.LeftProjection.equivalence u v X.p).counitIso
    (counit.isHomLift u v X)

/-- Explicit universe-polymorphic quasi-inverse data over `C` for pullback reassociation. -/
def quasiInverse : BasedFunctor.QuasiInverse (forwardBased u v X) where
  inverse := inverseBased u v X
  unitIso := unitIso u v X
  counitIso := counitIso u v X

/-- The based forward comparison is an equivalence over `C`. -/
instance forwardBased.isEquivalence : (forwardBased u v X).IsEquivalence :=
  (quasiInverse u v X).isEquivalence

/-- The based inverse comparison is an equivalence over `C`. -/
instance inverseBased.isEquivalence : (inverseBased u v X).IsEquivalence :=
  (quasiInverse u v X).symm.isEquivalence

section StableUniverse

universe u v₀ w vT

variable {C₀ D₀ E₀ : Type u}
variable [Category.{v₀} C₀] [Category.{v₀} D₀] [Category.{v₀} E₀]

/-- On a common universe layer, the explicit based quasi-inverse packages into the canonical
bicategorical equivalence over the leftmost base. -/
def basedEquivalence
    (u₀ : C₀ ⥤ D₀) (v₀' : D₀ ⥤ E₀)
    (X₀ : FiberedCategoryOver.{u, v₀, w, vT} E₀) :
    (FiberedCategoryOver.pullback u₀
        (FiberedCategoryOver.pullback v₀' X₀)).toBasedCategory ≌
      (FiberedCategoryOver.pullback (u₀ ⋙ v₀') X₀).toBasedCategory :=
  (quasiInverse u₀ v₀' X₀).toEquivalence

end StableUniverse

end CategoryTheory.FiberedCategoryOver.Pullback.Comp
