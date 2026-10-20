/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cocontinuous site functors with adjoints

This leaf records the canonical descriptions of the direct and inverse image
functors induced by a cocontinuous functor of sites that is equipped with an
adjoint. The declarations are independent of a particular slice-site or
descent presentation.
-/

@[expose] public section

open CategoryTheory Functor Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace IsLeftAdjoint

/-- A left adjoint has the pointwise right Kan extensions needed to define
the cocontinuous direct image on `Type`-valued sheaves. -/
@[stacks 00XX "right Kan extensions"]
instance hasPointwiseRightKanExtension
    (u : C ⥤ D) [u.IsLeftAdjoint] (P : Cᵒᵖ ⥤ Type w) :
    u.op.HasPointwiseRightKanExtension P := sorry

end IsLeftAdjoint

namespace IsRightAdjoint

/-- A right adjoint has the pointwise left Kan extensions needed to express
the cocontinuous inverse image as a sheafified left Kan extension. -/
@[stacks 00XX "left Kan extensions"]
instance hasPointwiseLeftKanExtension
    (v : D ⥤ C) [v.IsRightAdjoint] (P : Dᵒᵖ ⥤ Type w) :
    v.op.HasPointwiseLeftKanExtension P := sorry

end IsRightAdjoint

namespace CocontinuousPushforward

variable {u : C ⥤ D} {v : D ⥤ C}

/-- The underlying presheaf of cocontinuous direct image along `u` is
precomposition by a specified right adjoint `v`. -/
@[stacks 00XX "direct image"]
noncomputable def rightAdjointIso
    [u.IsCocontinuous J K] (adj : u ⊣ v) (ℱ : Sheaf J (Type w)) :
    letI : u.IsLeftAdjoint := adj.isLeftAdjoint
    ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).1 ≅ v.op ⋙ ℱ.1 :=
  letI : u.IsLeftAdjoint := adj.isLeftAdjoint
  (u.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type w) J K).app ℱ ≪≫
    ((u.op.ranAdjunction (Type w)).rightAdjointUniq
      (adj.op.whiskerLeft (Type w))).app ℱ.1

/-- Each component of `rightAdjointIso` is invertible. -/
@[stacks 00XX "direct image"]
theorem rightAdjointIso_hom_app_isIso
    [u.IsCocontinuous J K] (adj : u ⊣ v) (ℱ : Sheaf J (Type w)) (V : D) :
    IsIso ((rightAdjointIso (J := J) (K := K) adj ℱ).hom.app (op V)) := sorry

end CocontinuousPushforward

namespace CocontinuousPullback

variable {u : C ⥤ D} {v : D ⥤ C}

/-- Cocontinuous inverse image along `u` is the sheafification of the left
Kan extension along a specified right adjoint `v`. -/
@[stacks 00XX "inverse image"]
noncomputable def rightAdjointSheafifyLanIso
    [HasWeakSheafify J (Type w)] (adj : u ⊣ v) (𝒢 : Sheaf K (Type w)) :
    letI : v.IsRightAdjoint := adj.isRightAdjoint
    (u.sheafPullbackCocontinuous (Type w) J K).obj 𝒢 ≅
      (presheafToSheaf J (Type w)).obj ((v.op.lan).obj 𝒢.1) :=
  letI : v.IsRightAdjoint := adj.isRightAdjoint
  (presheafToSheaf J (Type w)).mapIso
    (((adj.op.whiskerLeft (Type w)).leftAdjointUniq
      (v.op.lanAdjunction (Type w))).app 𝒢.1)

/-- The canonical inverse-image comparison to the sheafified left Kan
extension is invertible. -/
@[stacks 00XX "inverse image"]
theorem rightAdjointSheafifyLanIso_hom_isIso
    [HasWeakSheafify J (Type w)] (adj : u ⊣ v) (𝒢 : Sheaf K (Type w)) :
    IsIso (rightAdjointSheafifyLanIso (J := J) (K := K) adj 𝒢).hom := sorry

end CocontinuousPullback

end CategoryTheory.Functor
