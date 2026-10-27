/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedDescent

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/- Lemma 85.17.3: For a site with equalizers and fibre products and a hypercovering,
the canonical map `E ⟶ Ra_* a⁻¹ E` is an isomorphism for every `E ∈ D(C)`. -/
@[stacks 0D8G] #check (CategoryTheory.SemiRepresentableFamily.derivedUnit_app_isIso J K :
  ∀ E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}),
    IsIso ((derivedUnit J K).app E))

end CategoryTheory.SemiRepresentableFamily
