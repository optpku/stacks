/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Second-projection comparison for the pseudo-pullback swap

This leaf identifies the second projection after swapping with the original first projection.
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

/-- The objectwise comparison from the second projection after swapping to the original first
projection. The two explicit objects agree, so its component is the identity isomorphism. -/
def swap.sndIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap F G ⋙ PseudoPullback.snd G F).obj P ≅ (PseudoPullback.fst F G).obj P :=
  Iso.refl _

/-- The second-projection comparisons for swap are natural in pseudo-pullback morphisms. -/
theorem swap.sndIsoApp.naturality
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (swap F G ⋙ PseudoPullback.snd G F).map φ ≫ (swap.sndIsoApp F G Q).hom =
      (swap.sndIsoApp F G P).hom ≫ (PseudoPullback.fst F G).map φ := sorry

/-- Every forward second-projection comparison for swap is vertical over the identity common
base map. -/
theorem swap.sndIsoApp.isHomLift
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    X.p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      (swap.sndIsoApp F G P).hom := sorry

/-- Componentwise isomorphism identifying the second projection after swap with the original
first projection. Its non-`Prop` components are identities. -/
@[stacks 0040 "second projection comparison for the explicit pseudo-pullback swap"]
def swap.sndIso (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap F G ⋙ PseudoPullback.snd G F ≅ PseudoPullback.fst F G :=
  BasedNatIso.ofComponents
    (swap.sndIsoApp F G)
    (fun φ ↦ swap.sndIsoApp.naturality F G φ)
    (swap.sndIsoApp.isHomLift F G)

/-- The forward component of the second-projection comparison for swap is the identity. -/
@[simp]
theorem swap.sndIso.hom.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.sndIso F G).hom.toNatTrans.app P =
      (swap.sndIsoApp F G P).hom := sorry

/-- The inverse component of the second-projection comparison for swap is the identity. -/
@[simp]
theorem swap.sndIso.inv.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.sndIso F G).inv.toNatTrans.app P =
      (swap.sndIsoApp F G P).inv := sorry

end

end PseudoPullback
end BasedCategory
end CategoryTheory
