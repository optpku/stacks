module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_8_2_Operations

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

/-- Lemma 62.6.2 (1): if `α` is a relative `r`-cycle on `X / S`, then any
restriction of `α` to a morphism of opens `φ : U ⟶ V` over `f` is a relative
`r`-cycle. -/
@[stacks 0H51]
theorem isRelative_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) [LocallyOfFiniteType φ]
    (hφ : φ ≫ V.ι = U.ι ≫ f) :
    IsRelative (restrict U V φ hφ α) := sorry

/-- Lemma 62.6.2 (2): if `α` is a relative `r`-cycle on `X / S`, then any base
change `g^*α` of `α` along `g : S' ⟶ S` is a relative `r`-cycle. -/
@[stacks 0H51]
theorem isRelative_baseChange {X S S' : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    {r : ℕ} {α : Family f r} (hα : IsRelative α) (g : S' ⟶ S) :
    IsRelative (baseChange f g r α) := sorry

/-- Lemma 62.6.2 (3): if `α` is a relative `r`-cycle on `X / S`, then any flat
pullback `p^*α` of `α` along a flat morphism of relative dimension `e` is a
relative `r`-cycle. -/
@[stacks 0H51]
theorem isRelative_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (p : X' ⟶ X) (e : ℕ)
    [Flat p] [Scheme.Hom.RelativeDimension p e] :
    IsRelative (flatPullback p e α) := sorry

/-- Lemma 62.6.2 (4): if `α` is a relative `r`-cycle on `X / S`, then any proper
pushforward `h_*α` of `α` along a proper morphism over `S` is a relative
`r`-cycle. -/
@[stacks 0H51]
theorem isRelative_pushforward {X Y S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (pY : Y ⟶ S) [LocallyOfFiniteType pY] (h : X ⟶ Y)
    [IsProper h] (hc : h ≫ pY = f) :
    IsRelative (pushforward pY h hc α) := sorry

end AlgebraicGeometry.RelativeCycle
