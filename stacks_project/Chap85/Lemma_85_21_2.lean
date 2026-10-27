/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.CategoryTheory.Sites.Hypercovering.DerivedAdjunction
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedDescent
import StacksCheckRecall

/-!
# Lemma 85.21.2

Let `C` be a site with fibre products and `X` an object of `C`. Let
`a : U ⟶ X` be a hypercovering of `X` in `C`. For every `E` in `D(C / X)`,
the canonical derived-unit map `E ⟶ Ra_* a⁻¹ E` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
variable (hA : A.IsHypercovering J)
variable [HasSheafify (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/- Lemma 85.21.2: Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C` as defined above. For
`E ∈ D(C / X)` the map `E ⟶ Ra_* a⁻¹ E` is an isomorphism. -/
@[stacks 0D8N] #check
  (CategoryTheory.SemiRepresentableFamily.derivedUnit_app_isIso.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right
      (toHypercovering.{w} A hA)) :
    ∀ E : DerivedCategory (Sheaf (J.over A.right) AddCommGrpCat.{max w u v}),
      IsIso ((CategoryTheory.Hypercovering.derivedUnit J A.right
        (toHypercovering.{w} A hA)).app E))

/- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism of functors on `D(C / X)`. -/
#check
  (CategoryTheory.SemiRepresentableFamily.derivedUnit_isIso.{w, v, max u v}
    (J.over A.right) (CategoryTheory.Hypercovering.toSliceTerminal J A.right
      (toHypercovering.{w} A hA)) :
    IsIso (CategoryTheory.Hypercovering.derivedUnit J A.right (toHypercovering.{w} A hA)))

end CategoryTheory.SimplicialObject.Augmented
