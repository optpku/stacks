/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison.Forward.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forward projection comparisons for fibres of based pseudo-pullbacks

This leaf records how the concrete comparison from an actual pseudo-pullback fibre to its
categorical-pullback model preserves both projections. It depends only on the concrete comparison,
so consumers do not need to import the packaged equivalence.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

noncomputable section

namespace PseudoPullback
namespace Fiber

/-- The objectwise first-projection comparison for the concrete fibre comparison. -/
def comparison.fstIsoApp :
    ∀ {U : C} (P : Functor.Fiber (PseudoPullback F G).p U),
      (Fiber.comparison F G U ⋙
          π₁ (F.fiberFunctor U) (G.fiberFunctor U)).obj P ≅
        ((PseudoPullback.fst F G).fiberFunctor U).obj P
  | _, ⟨_, rfl⟩ => Iso.refl _

/-- The first-projection comparisons are natural in morphisms of the actual fibre. -/
theorem comparison.fstIsoApp.naturality
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    (Fiber.comparison F G U ⋙
        π₁ (F.fiberFunctor U) (G.fiberFunctor U)).map φ ≫
        (comparison.fstIsoApp F G Q).hom =
      (comparison.fstIsoApp F G P).hom ≫
        ((PseudoPullback.fst F G).fiberFunctor U).map φ := sorry

/-- The concrete fibre comparison preserves the first projection. -/
@[stacks 02XI "first projection comparison for the concrete fibre comparison"]
def comparison.fstIso (U : C) :
    Fiber.comparison F G U ⋙
        π₁ (F.fiberFunctor U) (G.fiberFunctor U) ≅
      (PseudoPullback.fst F G).fiberFunctor U :=
  NatIso.ofComponents
    (comparison.fstIsoApp F G)
    (fun φ ↦ comparison.fstIsoApp.naturality F G φ)

/-- The forward component of the first-projection isomorphism is its explicit component. -/
@[simp]
theorem comparison.fstIso.hom.app
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (comparison.fstIso F G U).hom.app P =
      (comparison.fstIsoApp F G P).hom := sorry

/-- The inverse component of the first-projection isomorphism is its explicit component. -/
@[simp]
theorem comparison.fstIso.inv.app
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (comparison.fstIso F G U).inv.app P =
      (comparison.fstIsoApp F G P).inv := sorry

/-- The objectwise second-projection comparison for the concrete fibre comparison. -/
def comparison.sndIsoApp :
    ∀ {U : C} (P : Functor.Fiber (PseudoPullback F G).p U),
      (Fiber.comparison F G U ⋙
          π₂ (F.fiberFunctor U) (G.fiberFunctor U)).obj P ≅
        ((PseudoPullback.snd F G).fiberFunctor U).obj P
  | _, ⟨_, rfl⟩ => Iso.refl _

/-- The second-projection comparisons are natural in morphisms of the actual fibre. -/
theorem comparison.sndIsoApp.naturality
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    (Fiber.comparison F G U ⋙
        π₂ (F.fiberFunctor U) (G.fiberFunctor U)).map φ ≫
        (comparison.sndIsoApp F G Q).hom =
      (comparison.sndIsoApp F G P).hom ≫
        ((PseudoPullback.snd F G).fiberFunctor U).map φ := sorry

/-- The concrete fibre comparison preserves the second projection. -/
@[stacks 02XI "second projection comparison for the concrete fibre comparison"]
def comparison.sndIso (U : C) :
    Fiber.comparison F G U ⋙
        π₂ (F.fiberFunctor U) (G.fiberFunctor U) ≅
      (PseudoPullback.snd F G).fiberFunctor U :=
  NatIso.ofComponents
    (comparison.sndIsoApp F G)
    (fun φ ↦ comparison.sndIsoApp.naturality F G φ)

/-- The forward component of the second-projection isomorphism is its explicit component. -/
@[simp]
theorem comparison.sndIso.hom.app
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (comparison.sndIso F G U).hom.app P =
      (comparison.sndIsoApp F G P).hom := sorry

/-- The inverse component of the second-projection isomorphism is its explicit component. -/
@[simp]
theorem comparison.sndIso.inv.app
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (comparison.sndIso F G U).inv.app P =
      (comparison.sndIsoApp F G P).inv := sorry

end Fiber
end PseudoPullback
end

end BasedCategory
end CategoryTheory
