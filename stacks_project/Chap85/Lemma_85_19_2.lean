/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.DerivedAdjunction
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedDescent

/-!
# Lemma 85.19.2

Let `C` be a site with fibre products and `X` an object of `C`. Let `K` be a
hypercovering of `X`. For every `E` in `D(C / X)`, the canonical derived-unit map
`E ⟶ Ra_* a⁻¹ E` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/- Lemma 85.19.2: For every `E ∈ D(C / X)`, the canonical map
`E ⟶ Ra_* a⁻¹ E` is an isomorphism. -/
@[stacks 0D8L] #check
  (CategoryTheory.SemiRepresentableFamily.derivedUnit_app_isIso.{w, v, max u v}
    (J.over X) (CategoryTheory.Hypercovering.toSliceTerminal J X K) :
    ∀ E : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}),
      IsIso ((CategoryTheory.Hypercovering.derivedUnit J X K).app E))

#check (CategoryTheory.SemiRepresentableFamily.derivedUnit_isIso.{w, v, max u v}
  (J.over X) (CategoryTheory.Hypercovering.toSliceTerminal J X K) :
  IsIso (CategoryTheory.Hypercovering.derivedUnit J X K))

end CategoryTheory.Hypercovering
