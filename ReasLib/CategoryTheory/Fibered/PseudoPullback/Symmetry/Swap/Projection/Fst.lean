/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# First-projection comparison for the pseudo-pullback swap

This leaf identifies the first projection after swapping with the original second projection.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace PseudoPullback

noncomputable section

/-- The objectwise comparison from the first projection after swapping to the original second
projection. The two explicit objects agree, so its component is the identity isomorphism. -/
def swap.fstIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap F G ⋙ PseudoPullback.fst G F).obj P ≅ (PseudoPullback.snd F G).obj P :=
  Iso.refl _

/-- The first-projection comparisons for swap are natural in pseudo-pullback morphisms. -/
theorem swap.fstIsoApp.naturality
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (swap F G ⋙ PseudoPullback.fst G F).map φ ≫ (swap.fstIsoApp F G Q).hom =
      (swap.fstIsoApp F G P).hom ≫ (PseudoPullback.snd F G).map φ := sorry

/-- Every forward first-projection comparison for swap is vertical over the identity common
base map. -/
theorem swap.fstIsoApp.isHomLift
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    Y.p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      (swap.fstIsoApp F G P).hom := sorry

/-- Componentwise isomorphism identifying the first projection after swap with the original
second projection. Its non-`Prop` components are identities. -/
@[stacks 0040 "first projection comparison for the explicit pseudo-pullback swap"]
def swap.fstIso (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap F G ⋙ PseudoPullback.fst G F ≅ PseudoPullback.snd F G :=
  BasedNatIso.ofComponents
    (swap.fstIsoApp F G)
    (fun φ ↦ swap.fstIsoApp.naturality F G φ)
    (swap.fstIsoApp.isHomLift F G)

/-- The forward component of the first-projection comparison for swap is the identity. -/
@[simp]
theorem swap.fstIso.hom.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.fstIso F G).hom.toNatTrans.app P =
      (swap.fstIsoApp F G P).hom := sorry

/-- The inverse component of the first-projection comparison for swap is the identity. -/
@[simp]
theorem swap.fstIso.inv.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.fstIso F G).inv.toNatTrans.app P =
      (swap.fstIsoApp F G P).inv := sorry

end

end PseudoPullback
end BasedCategory
end CategoryTheory
