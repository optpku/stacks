/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap07.Definition_7_14_1

import StacksCheckRecall

@[expose] public section

/-!
# Definition 7.14.5

Composition of exact morphisms of sites is already owned by
`IsExactMorphismOfSites.comp`; this file is a tagged recall.
-/

/- Definition 7.14.5: if `f : 𝒞₁ ⟶ 𝒞₂` and `g : 𝒞₂ ⟶ 𝒞₃` are morphisms of sites
given by continuous functors `u : 𝒞₂ ⥤ 𝒞₁` and `v : 𝒞₃ ⥤ 𝒞₂`, the composite
`g ∘ f` is the morphism of sites presented by `u ∘ v`. Unbundled morphisms of
sites are functors plus `IsExactMorphismOfSites`; composition is functor
composition together with `IsExactMorphismOfSites.comp`. Identifying `C = 𝒞₃`,
`D = 𝒞₂`, `E = 𝒞₁` and Lean binders `u_lean = v`, `v_lean = u` recovers
`u_lean ⋙ v_lean = v ⋙ u = u ∘ v`. The middle topology remains an explicit
parameter of the canonical API. -/
@[stacks 03CC] #check CategoryTheory.IsExactMorphismOfSites.comp

#check CategoryTheory.Functor.isContinuous_comp
