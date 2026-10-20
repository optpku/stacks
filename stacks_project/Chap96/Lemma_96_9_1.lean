module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverPostScheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 96.9.1: let `p : 𝒳 ⥤ Over S` be a category fibred in groupoids,
and let `x` lie over `U = (p.obj x).left`. For each
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the induced functor is an
equivalence of sites `𝒳_τ / x ⟶ (Sch/U)_τ`. The dense-subsite assertion below
and the category-equivalence assertion following it jointly express this
equivalence of sites. -/
@[stacks 06W0]
#check (CategoryTheory.Functor.overPostScheme.isDenseSubsite :
  ∀ {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳)
    (τ : StandardTopology),
    (Functor.overPostScheme p x).IsDenseSubsite
      ((p.inheritedTopology (τ.overTopology S)).over x)
      (τ.overTopology (p.obj x).left))

#check (CategoryTheory.Functor.overPostScheme.isEquivalence :
  ∀ {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳),
    (Functor.overPostScheme p x).IsEquivalence)

#check (CategoryTheory.Functor.overPostScheme :
  ∀ {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) (x : 𝒳), Over x ⥤ Over (p.obj x).left)

#check (CategoryTheory.Functor.overPostScheme.covering_iff :
  ∀ {S : Scheme.{u}} {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (x : 𝒳)
    (τ : StandardTopology) {y : Over x} (R : Sieve y),
    R ∈ (p.inheritedTopology (τ.overTopology S)).over x y ↔
      R.functorPushforward (Functor.overPostScheme p x) ∈
        τ.overTopology (p.obj x).left ((Functor.overPostScheme p x).obj y))

