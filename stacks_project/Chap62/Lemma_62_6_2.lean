module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Functoriality
public import ReasLib.AlgebraicGeometry.RelativeCycle.BaseChange
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Functoriality of relative cycles

Restriction, base change, flat pullback, and proper pushforward preserve
the relative-cycle condition on families of fibrewise `r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.2 (1): if `α` is a relative `r`-cycle on `X / S`, then any
restriction of `α` to a morphism of opens `φ : U ⟶ V` over `f` is a relative
`r`-cycle. -/
@[stacks 0H51] #check (AlgebraicGeometry.RelativeCycle.isRelative_restrict :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r}, IsRelative α → ∀ (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) [LocallyOfFiniteType φ]
    (hφ : φ ≫ V.ι = U.ι ≫ f),
    IsRelative (restrict U V φ hφ α))

/- Lemma 62.6.2 (2): if `α` is a relative `r`-cycle on `X / S`, then any base
change `g^*α` of `α` along `g : S' ⟶ S` is a relative `r`-cycle. -/
@[stacks 0H51] #check (AlgebraicGeometry.RelativeCycle.groupBaseChange_mem :
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : group f r),
    FamilyOfCyclesOnFibres.baseChange f g r (α : f.FiberCycleFamily r) ∈
      group (pullback.snd f g) r)

/- Lemma 62.6.2 (3): if `α` is a relative `r`-cycle on `X / S`, then any flat
pullback `p^*α` of `α` along a flat morphism of relative dimension `e` is a
relative `(r + e)`-cycle. -/
@[stacks 0H51] #check (AlgebraicGeometry.RelativeCycle.isRelative_flatPullback :
  ∀ {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r}, IsRelative α → ∀ (p : X' ⟶ X) (e : ℕ)
    [Flat p] [Scheme.Hom.RelativeDimension p e],
    IsRelative (flatPullback p e α))

/- Lemma 62.6.2 (4): if `α` is a relative `r`-cycle on `X / S`, then any proper
pushforward `h_*α` of `α` along a proper morphism over `S` is a relative
`r`-cycle. -/
@[stacks 0H51] #check (AlgebraicGeometry.RelativeCycle.isRelative_properPushforward :
  ∀ {X Y S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α : f.FiberCycleFamily r}, IsRelative α → ∀ (pY : Y ⟶ S)
    [LocallyOfFiniteType pY] (h : X ⟶ Y)
    [IsProper h] (hc : h ≫ pY = f),
    IsRelative (pushforward pY h hc α))

end AlgebraicGeometry.RelativeCycle
