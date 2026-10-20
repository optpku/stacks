/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import Mathlib.CategoryTheory.Sites.Pullback

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe t u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [∀ (ℱ : Cᵒᵖ ⥤ Type t), u.op.HasLeftKanExtension ℱ]
variable [HasWeakSheafify K (Type t)]

/- Domain-style sampling for Lemma 7.13.3:
- primary domain: inverse-image/direct-image adjunctions for continuous functors of sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionContinuous`;
- source/core/bridge triage:
  `source-facing`: the sheafified left Kan extension along `u.op`;
  `core/canonical`: the constructed adjunction owner
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`;
  `bridge/view`: the abstract adjunction owner `Functor.sheafAdjunctionContinuous`,
  compared via `Functor.sheafPullbackConstruction.sheafPullbackIso`.

The primitive data are continuity, left Kan extensions, and weak sheafification; the adjunction is
derived API and should be recalled directly from the owner theorem. -/
/- Lemma 7.13.3: in the situation of Lemma 7.13.2, the functor sending a sheaf `𝒢` on
`(𝒞, J)` to the sheafification of its presheaf left Kan extension along `u.op` on `(𝒟, K)` is left
adjoint to the canonical inverse-image functor on sheaves. -/
@[stacks 00WX] #check @Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

end
