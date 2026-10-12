/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object computations for explicit pseudo-pullback maps

Formulas for the common base, endpoint projections, and comparison isomorphism of a mapped
pseudo-pullback object.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- The induced pseudo-pullback map retains the common base object. -/
@[simp]
theorem map.obj.base
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    baseObj ((map ψ).obj P) = baseObj P := sorry
/- Proof strategy: unfold the public `map` owner through its private object constructor and read
the public `baseObj` projection of `mk`. -/

/-- The first object projection of an induced pseudo-pullback map is the image under the left
component of the cospan transformation. -/
@[simp]
theorem map.obj.fst
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    fstObj ((map ψ).obj P) = ψ.left.obj (fstObj P) := sorry
/- Proof strategy: unfold only the public owner and read the first object projection of the
privately assembled `PseudoPullback.mk`. -/

/-- The second object projection of an induced pseudo-pullback map is the image under the right
component of the cospan transformation. -/
@[simp]
theorem map.obj.snd
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    sndObj ((map ψ).obj P) = ψ.right.obj (sndObj P) := sorry
/- Proof strategy: unfold only the public owner and read the second object projection of the
privately assembled `PseudoPullback.mk`. -/

/-- The objectwise comparison isomorphism of an induced pseudo-pullback map is the ambient image
of the canonical three-step comparison in the standard fiber. -/
@[simp, stacks 0040 "mapped pseudo-pullback object comparison isomorphism"]
theorem map.obj.comparisonIso
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    PseudoPullback.comparisonIsoApp (F := F₂) (G := G₂) ((map ψ).obj P) =
      (Functor.Fiber.fiberInclusion :
        S₂.p.Fiber (baseObj P) ⥤ S₂.obj).mapIso
        ((BasedNatIso.fiber ψ.leftIso (baseObj P)).app (fiberObj P).fst ≪≫
          (ψ.base.fiberFunctor (baseObj P)).mapIso (fiberObj P).iso ≪≫
            (BasedNatIso.fiber ψ.rightIso (baseObj P)).symm.app
              (fiberObj P).snd) := sorry

/-- The forward map of the comparison isomorphism of a mapped pseudo-pullback object is the
ambient image of the canonical three-step fibre comparison. -/
@[simp]
theorem map.obj.comparisonIso.hom
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback.comparisonIsoApp (F := F₂) (G := G₂) ((map ψ).obj P)).hom =
      ((Functor.Fiber.fiberInclusion :
        S₂.p.Fiber (baseObj P) ⥤ S₂.obj).mapIso
        ((BasedNatIso.fiber ψ.leftIso (baseObj P)).app (fiberObj P).fst ≪≫
          (ψ.base.fiberFunctor (baseObj P)).mapIso (fiberObj P).iso ≪≫
            (BasedNatIso.fiber ψ.rightIso (baseObj P)).symm.app
              (fiberObj P).snd)).hom := sorry

/-- The inverse map of the comparison isomorphism of a mapped pseudo-pullback object is the
ambient image of the inverse canonical three-step fibre comparison. -/
@[simp]
theorem map.obj.comparisonIso.inv
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback.comparisonIsoApp (F := F₂) (G := G₂) ((map ψ).obj P)).inv =
      ((Functor.Fiber.fiberInclusion :
        S₂.p.Fiber (baseObj P) ⥤ S₂.obj).mapIso
        ((BasedNatIso.fiber ψ.leftIso (baseObj P)).app (fiberObj P).fst ≪≫
          (ψ.base.fiberFunctor (baseObj P)).mapIso (fiberObj P).iso ≪≫
            (BasedNatIso.fiber ψ.rightIso (baseObj P)).symm.app
              (fiberObj P).snd)).inv := sorry

/-- The target comparison stored by an induced pseudo-pullback map is the canonical three-step
pasting of the left boundary comparison, the mapped source comparison, and the inverse right
boundary comparison. -/
@[simp]
theorem map.obj.comparison
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    comparison ((map ψ).obj P) =
      ((BasedNatIso.fiber ψ.leftIso (baseObj P)).app (fiberObj P).fst ≪≫
        (ψ.base.fiberFunctor (baseObj P)).mapIso (fiberObj P).iso ≪≫
          (BasedNatIso.fiber ψ.rightIso (baseObj P)).symm.app
            (fiberObj P).snd).hom.1 := sorry
/- Proof strategy: expose the public `comparison` projection of the mapped object; its private
constructor stores exactly this symmetric three-step fiber isomorphism. -/

end
end PseudoPullback

end BasedCategory

end CategoryTheory
