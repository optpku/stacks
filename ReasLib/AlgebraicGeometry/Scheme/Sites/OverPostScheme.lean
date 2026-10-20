module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.InGroupoids

/-!
# Localizing a groupoid fibration at an object

A groupoid-fibred projection `p : 𝒳 ⥤ Over S` induces a functor from the slice
`Over x` to the big site of the scheme `U = (p.obj x).left`. For each standard
topology `τ`, this functor is an equivalence of sites from the inherited slice
site to `(Sch/U)_τ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace CategoryTheory.Functor

/-- The functor `Over x ⥤ Over U` induced by a projection `p : 𝒳 ⥤ Over S`,
where `U = (p.obj x).left`. It is postcomposition with `p` followed by the
iterated-slice comparison `Over (p.obj x) ⥤ Over U`. -/
def overPostScheme {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) (x : 𝒳) :
    Over x ⥤ Over (p.obj x).left :=
  Over.post p ⋙ (p.obj x).iteratedSliceForward

namespace overPostScheme

/-- `overPostScheme p x` agrees with postcomposition along `p ⋙ Over.forget S`. -/
theorem eq_post_forget {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) (x : 𝒳) :
    overPostScheme p x = Over.post (p ⋙ Over.forget S) :=
  sorry

/-- A groupoid-fibred projection induces an equivalence of categories
`Over x ≌ Over U` with `U = (p.obj x).left`. -/
instance isEquivalence {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳) :
    (overPostScheme p x).IsEquivalence :=
  sorry

/-- For each standard topology `τ`, `overPostScheme p x` exhibits the inherited
slice site as a dense subsite of the big `τ`-site of `U = (p.obj x).left`. -/
instance isDenseSubsite {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳)
    (τ : StandardTopology) :
    (overPostScheme p x).IsDenseSubsite
      ((p.inheritedTopology (τ.overTopology S)).over x)
      (τ.overTopology ((p.obj x).left)) :=
  sorry

/-- For each standard topology `τ`, `overPostScheme p x` is a morphism of sites
from the inherited slice site to the big `τ`-site of `U`. -/
instance isMorphismOfSites {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳)
    (τ : StandardTopology) :
    IsMorphismOfSites ((p.inheritedTopology (τ.overTopology S)).over x)
      (τ.overTopology ((p.obj x).left)) (overPostScheme p x) :=
  sorry

/-- A sieve on the inherited slice site is covering if and only if its image
under `overPostScheme p x` covers in the big `τ`-site of `U`. -/
theorem covering_iff {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳)
    (τ : StandardTopology) {y : Over x} (R : Sieve y) :
    R ∈ (p.inheritedTopology (τ.overTopology S)).over x y ↔
      R.functorPushforward (overPostScheme p x) ∈
        τ.overTopology ((p.obj x).left) ((overPostScheme p x).obj y) :=
  sorry

end overPostScheme

end CategoryTheory.Functor
