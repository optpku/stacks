module

public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites

import StacksCheckRecall

@[expose] public section

/-!
# Definition 7.14.5

Composition of exact morphisms of sites is already owned by
`IsExactMorphismOfSites.comp`; this file is a tagged recall.
-/

universe u₁ u₂ u₃ v₁ v₂ v₃ w

open CategoryTheory

/- Definition 7.14.5: if `f : 𝒞₁ ⟶ 𝒞₂` and `g : 𝒞₂ ⟶ 𝒞₃` are morphisms of sites
given by continuous functors `u : 𝒞₂ ⥤ 𝒞₁` and `v : 𝒞₃ ⥤ 𝒞₂`, the composite
`g ∘ f` is the morphism of sites presented by `u ∘ v`. Unbundled morphisms of
sites are functors plus `IsExactMorphismOfSites`; composition is functor
composition together with `IsExactMorphismOfSites.comp`. Identifying `C = 𝒞₃`,
`D = 𝒞₂`, `E = 𝒞₁` and Lean binders `u_lean = v`, `v_lean = u` recovers
`u_lean ⋙ v_lean = v ⋙ u = u ∘ v`. The middle topology remains an explicit
parameter of the canonical API. -/
@[stacks 03CC] #check
  (CategoryTheory.IsExactMorphismOfSites.comp :
    ∀ {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
      {E : Type u₃} [Category.{v₃} E]
      {J : GrothendieckTopology C} (K : GrothendieckTopology D) {L : GrothendieckTopology E}
      (u : C ⥤ D) (v : D ⥤ E) [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
      [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
      [∀ Q : Dᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension Q]
      [∀ P : Cᵒᵖ ⥤ Type w, (u ⋙ v).op.HasLeftKanExtension P]
      [IsExactMorphismOfSites J K u] [IsExactMorphismOfSites K L v],
      IsExactMorphismOfSites J L (u ⋙ v))

#check CategoryTheory.Functor.isContinuous_comp
