module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Localization
import StacksCheckRecall

/-!
# Lemma 96.9.4

The site equivalence of Lemma 96.9.1 extends to an equivalence of ringed
sites between the slice `(𝒳_τ / x, 𝒪_𝒳|_x)` and `((Sch/U)_τ, 𝒪)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 96.9.4: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Let `x` be an object of
`𝒳` lying over `U = p(x)`. The functor of Lemma 96.9.1 extends to an
equivalence of ringed sites
`(𝒳_τ / x, 𝒪_𝒳|_x) ≃ ((Sch/U)_τ, 𝒪)`, as the morphism
`GroupoidsOver.overPostSchemeRingedSiteHom 𝒳 τ x`, whose base is
`CategoryTheory.Functor.overPostScheme 𝒳.p x`. -/
@[stacks 06W9]
#check (AlgebraicGeometry.GroupoidsOver.overPostSchemeRingedSiteHom_isEquivalence :
  ∀ {S : Scheme.{u}} (𝒳 : GroupoidsOver S) (τ : StandardTopology) (x : 𝒳.total),
    RingedSiteMap.IsEquivalence
      (AlgebraicGeometry.GroupoidsOver.overPostSchemeRingedSiteHom 𝒳 τ x))

