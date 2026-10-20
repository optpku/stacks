/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of sheafified representables

This leaf first records the general compatibility between left Kan extension, sheafification,
and sheaf pullback.  Specializing that data-level isomorphism to a lifted Yoneda presheaf gives
the canonical pullback isomorphism for sheafified representables.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Presheaf

universe w u₁ u₂ v₁ v₂ uA vA

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : Functor C D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {A : Type uA} [Category.{vA} A]
variable [u.IsContinuous J K]
variable [HasWeakSheafify J A] [HasWeakSheafify K A]
variable [∀ P : Functor Cᵒᵖ A, u.op.HasLeftKanExtension P]

/-- Left Kan extension followed by sheafification is canonically isomorphic to sheafification
followed by sheaf pullback. This data-level comparison comes from uniqueness of left adjoints;
neither direction is chosen from an `IsIso` proof. -/
noncomputable def lanSheafificationIso :
    u.op.lan ⋙ presheafToSheaf K A ≅
      presheafToSheaf J A ⋙ u.sheafPullback A J K :=
  let lanAdj := u.op.lanAdjunction A
  let pullbackAdj := u.sheafAdjunctionContinuous A J K
  let left := lanAdj.comp (sheafificationAdjunction K A)
  let right := (sheafificationAdjunction J A).comp pullbackAdj
  left.leftAdjointUniq
    (right.ofNatIsoRight (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K))

end CategoryTheory.Functor

namespace CategoryTheory.Functor.SheafifiedRepresentable

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : Functor C D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [HasWeakSheafify J (Type (max (max w u₁ v₁) v₂ u₂))]
variable [HasWeakSheafify K (Type (max (max w u₁ v₁) v₂ u₂))]
variable [∀ P : Functor Cᵒᵖ (Type (max (max w u₁ v₁) v₂ u₂)),
  u.op.HasLeftKanExtension P]

/-- The canonical pullback isomorphism for a lifted sheafified representable. Its inverse comes
from adjoint uniqueness in `Functor.lanSheafificationIso`, not from an `IsIso` witness. -/
@[stacks 04D3]
noncomputable def pullbackIso (U : C) :
    K.uliftSheafifiedRepresentable.{max w u₁ v₁, v₂, u₂} (u.obj U) ≅
      (u.sheafPullback (Type (max (max w u₁ v₁) v₂ u₂)) J K).obj
        (J.uliftSheafifiedRepresentable.{max (max w u₁ v₁) v₂ u₂, v₁, u₁} U) :=
  let A := Type (max (max w u₁ v₁) v₂ u₂)
  let P : Functor Cᵒᵖ A :=
    uliftYoneda.{max (max w u₁ v₁) v₂ u₂, v₁, u₁}.obj U
  Functor.mapIso (presheafToSheaf K A)
      ((compULiftYonedaIsoULiftYonedaCompLan.{max (max w u₁ v₁) v₂ u₂} u).app U) ≪≫
    (u.lanSheafificationIso J K).app P

/-- The forward map of the canonical pullback isomorphism for a lifted sheafified
representable. -/
noncomputable abbrev pullbackComparison (U : C) :
    K.uliftSheafifiedRepresentable.{max w u₁ v₁, v₂, u₂} (u.obj U) ⟶
      (u.sheafPullback (Type (max (max w u₁ v₁) v₂ u₂)) J K).obj
        (J.uliftSheafifiedRepresentable.{max (max w u₁ v₁) v₂ u₂, v₁, u₁} U) :=
  (pullbackIso u J K U).hom

end CategoryTheory.Functor.SheafifiedRepresentable
