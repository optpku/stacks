module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import stacks_project.Chap62.Definition_62_6_1_Specialization

/-!
# Descent of relative cycles along h coverings

A family of `r`-cycles on fibres of `X / S` is a relative cycle if and only if
every base change along an h covering of `S` is a relative cycle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- Each member of an h covering is locally of finite presentation. -/
instance HCovering.instLocallyOfFinitePresentation {T : Scheme.{u}} {ι : Type v}
    {family : ι → Over T} [h : HCovering family] (i : ι) :
    LocallyOfFinitePresentation (family i).hom :=
  h.locallyOfFinitePresentation i

/-- Sources of an h covering of a locally Noetherian scheme are locally
Noetherian. -/
instance HCovering.instIsLocallyNoetherian {S : Scheme.{u}} [IsLocallyNoetherian S]
    {ι : Type v} {family : ι → Over S} [HCovering family] (i : ι) :
    IsLocallyNoetherian (family i).left :=
  LocallyOfFiniteType.isLocallyNoetherian (family i).hom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.3: if `S` is locally Noetherian and `f : X ⟶ S` is locally of
finite type, then a family `α` of `r`-cycles on fibres of `X / S` is a
relative `r`-cycle if and only if every base change of `α` along an h
covering `{g_i : S_i ⟶ S}` is a relative `r`-cycle. -/
@[stacks 0H52]
theorem isRelative_iff_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : Family f r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    IsRelative α ↔ ∀ i, IsRelative (baseChange f (family i).hom r α) := sorry

/-- Base change of a relative `r`-cycle along every member of an h covering
remains a relative `r`-cycle. -/
theorem isRelative_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : Family f r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    IsRelative α → ∀ i, IsRelative (baseChange f (family i).hom r α) := sorry

/-- If every base change of a fibrewise family along an h covering is a
relative `r`-cycle, then the original family is a relative `r`-cycle. -/
theorem isRelative_of_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : Family f r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    (∀ i, IsRelative (baseChange f (family i).hom r α)) → IsRelative α := sorry

/-- A fibrewise family lies in `z(X/S, r)` if and only if each base change
along an h covering lies in `z(X_i/S_i, r)`. -/
theorem mem_group_iff_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : Family f r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    α ∈ group f r ↔
      ∀ i, baseChange f (family i).hom r α ∈
        group (pullback.snd f (family i).hom) r := sorry

end AlgebraicGeometry.RelativeCycle
