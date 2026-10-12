/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_8_1_Comparison
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 96.8.1

A category fibred in groupoids representable by a scheme is canonically
equivalent, as a ringed site, to the big site of that scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {𝒳 : GroupoidsOver S} {X : Over S}

/-- Lemma 96.8.1: let `S` be a scheme and let `𝒳` be a category fibred in
groupoids over `(Sch/S)`. Assume `𝒳` is representable by a scheme, exhibited
by an equivalence `e : 𝒳 ≌ slice X` with `X : Over S`. For each standard
topology `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` the associated
comparison `associatedRingedSiteHom e τ` is an equivalence of ringed sites
`(𝒳_τ, 𝒪_𝒳) ≃ ((Sch/X.left)_τ, 𝒪)`. -/
@[stacks 075I]
theorem associatedRingedSiteHom_isRingedEquivalence (e : 𝒳 ≌ slice X)
    (τ : StandardTopology) :
    (associatedRingedSiteHom e τ).IsRingedEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
