/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Comparison.Composition.Basic
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Equivalence
public import ReasLib.CategoryTheory.Fibered.Equivalence.StronglyCartesian

/-!
# Fibred equivalence for composition of pullback

On a common universe layer, the explicit based reassociation equivalence lifts to the
bicategory of fibred categories because both directions preserve strongly cartesian arrows.
-/

@[expose] public section

noncomputable section

open scoped CategoryTheory.Bicategory

namespace CategoryTheory.FiberedCategoryOver.Pullback.Comp

universe u v w vS

variable {C D E : Type u}
variable [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (u₀ : C ⥤ D) (v₀ : D ⥤ E)
variable (X : FiberedCategoryOver.{u, v, w, vS} E)

/-- Pullback along `u₀` after pullback along `v₀` is canonically equivalent, as a fibred
category over `C`, to pullback along `u₀ ⋙ v₀`. The supplied ambient based equivalence is
retained literally; no inverse data are selected from an existence proposition. -/
def equivalence :
    FiberedCategoryOver.pullback u₀ (FiberedCategoryOver.pullback v₀ X) ≌
      FiberedCategoryOver.pullback (u₀ ⋙ v₀) X :=
  Bicategory.LocallyInducedBicategory.equivalenceMk
    (basedEquivalence u₀ v₀ X)
    (BasedFunctor.IsEquivalence.preservesStronglyCartesian
      (basedEquivalence u₀ v₀ X).hom)
    (BasedFunctor.IsEquivalence.preservesStronglyCartesian
      (basedEquivalence u₀ v₀ X).inv)

end CategoryTheory.FiberedCategoryOver.Pullback.Comp
