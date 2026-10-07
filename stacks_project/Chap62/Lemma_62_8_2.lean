module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_8_2_Effective
public import stacks_project.Chap62.Lemma_62_8_2_Operations

/-!
# Functoriality of effective relative cycles

Restriction, base change, flat pullback, and proper pushforward preserve
effectiveness of relative `r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.8.2 (1): if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then any
restriction of `α` to a morphism of opens `φ : U ⟶ V` over `f` is effective. -/
@[stacks 0H5S]
theorem isEffective_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (h_eff : IsEffective α) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) :
    IsEffective (restrict U V φ hφ α) := sorry

/-- Lemma 62.8.2 (2): if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then any
base change of `α` along `g : S' ⟶ S` is effective. -/
@[stacks 0H5S]
theorem isEffective_baseChange {X S S' : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (h_eff : IsEffective α) (g : S' ⟶ S) :
    IsEffective (baseChange f g r α) := sorry

/-- Lemma 62.8.2 (3): if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then any
flat pullback of `α` along a flat morphism of relative dimension `e` is
effective. -/
@[stacks 0H5S]
theorem isEffective_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (h_eff : IsEffective α) (p : X' ⟶ X) (e : ℕ)
    [Flat p] [Scheme.Hom.RelativeDimension p e] :
    IsEffective (flatPullback p e α) := sorry

/-- Lemma 62.8.2 (4): if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then any
proper pushforward of `α` along a proper morphism over `S` is effective. -/
@[stacks 0H5S]
theorem isEffective_pushforward {X Y S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (h_eff : IsEffective α) (pY : Y ⟶ S)
    [LocallyOfFiniteType pY] (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) :
    IsEffective (pushforward pY h hc α) := sorry

end AlgebraicGeometry.RelativeCycle
