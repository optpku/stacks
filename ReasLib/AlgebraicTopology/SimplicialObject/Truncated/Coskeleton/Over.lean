/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Preserves
public import ReasLib.CategoryTheory.Limits.Over.FiniteConnected
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08NJ

# Coskeletons in slice categories

At a nonzero truncation level, the slice forgetful functor is a specialization of the generic
finite-connected-limit functor API in `Truncated.coskeleton.comp`.  This yields the canonical
natural isomorphism between forgetting and taking a coskeleton.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C]

namespace forget

namespace coskeleton

/-- Lemma 14.19.14 (08NJ): for `k ≠ 0`, forgetting from a slice category commutes naturally
with the `k`-coskeleton functor. -/
@[stacks 08NJ "slice forgetful functor commutes with coskeleton"]
noncomputable def iso
    (X : C) (k : ℕ) [NeZero k] [HasFiniteConnectedLimits C] :
    (Truncated.cosk k :
        SimplicialObject.Truncated (Over X) k ⥤ SimplicialObject (Over X)) ⋙
          (SimplicialObject.whiskering (Over X) C).obj (forget X) ≅
      (SimplicialObject.Truncated.whiskering (Over X) C).obj (forget X) ⋙
        (Truncated.cosk k : SimplicialObject.Truncated C k ⥤ SimplicialObject C) :=
  SimplicialObject.Truncated.coskeleton.comp.iso (forget X) k

/-- The component of the slice forgetful coskeleton comparison at a truncated simplicial object
over `X`. -/
@[stacks 08NJ "slice forgetful coskeleton comparison component"]
noncomputable def isoApp
    (X : C) (k : ℕ) [NeZero k] [HasFiniteConnectedLimits C]
    (U : SimplicialObject.Truncated (Over X) k) :
    ((Truncated.cosk k).obj U) ⋙ forget X ≅
      (Truncated.cosk k).obj (U ⋙ forget X) :=
  SimplicialObject.Truncated.coskeleton.comp.isoApp (forget X) U

/-- The component of the natural slice coskeleton comparison agrees with the objectwise
comparison inherited from the generic preservation API. -/
@[stacks 08NJ "natural and objectwise slice coskeleton comparisons"]
theorem iso_app
    (X : C) (k : ℕ) [NeZero k] [HasFiniteConnectedLimits C]
    (U : SimplicialObject.Truncated (Over X) k) :
    (iso X k).app U = isoApp X k U := sorry

namespace isoApp

/-- The forward slice coskeleton comparison is compatible with the chosen right-Kan-extension
counits. -/
@[reassoc (attr := simp), stacks 08NJ "slice coskeleton comparison and counit"]
theorem hom_counit
    (X : C) (k : ℕ) [NeZero k] [HasFiniteConnectedLimits C]
    (U : SimplicialObject.Truncated (Over X) k)
    (a : (SimplexCategory.Truncated k)ᵒᵖ) :
    (isoApp X k U).hom.app ((SimplexCategory.Truncated.inclusion k).op.obj a) ≫
        ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
          (U ⋙ forget X)).app a =
      (forget X).map
        (((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit U).app a) := sorry

/-- The inverse slice coskeleton comparison is compatible with the chosen right-Kan-extension
counits. -/
@[reassoc (attr := simp), stacks 08NJ "inverse slice coskeleton comparison and counit"]
theorem inv_counit
    (X : C) (k : ℕ) [NeZero k] [HasFiniteConnectedLimits C]
    (U : SimplicialObject.Truncated (Over X) k)
    (a : (SimplexCategory.Truncated k)ᵒᵖ) :
    (isoApp X k U).inv.app ((SimplexCategory.Truncated.inclusion k).op.obj a) ≫
        (forget X).map
          (((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit U).app a) =
      ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
        (U ⋙ forget X)).app a := sorry

end isoApp

end coskeleton

end forget

end CategoryTheory.Over
