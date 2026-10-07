module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap62.Lemma_62_6_2

/-!
# Descent of relative cycles along flat pullbacks

A family of `r`-cycles on fibres of `X / S` is a relative cycle if and only if
each flat pullback along a jointly surjective family of flat morphisms of
relative dimension `e` is a relative cycle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.4: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` locally
Noetherian and `f` locally of finite type. Let `r, e ≥ 0` be integers. Let `α`
be a family of `r`-cycles on fibres of `X / S`. Let `{f_i : X_i ⟶ X}` be a
jointly surjective family of flat morphisms, locally of finite type, and of
relative dimension `e`. Then `α` is a relative `r`-cycle if and only if each
flat pullback `flatPullback (family i).hom e α` is a relative cycle. -/
@[stacks 0H53]
theorem isRelative_iff_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : Family f r) :
    IsRelative α ↔ ∀ i, IsRelative (flatPullback (family i).hom e α) :=
  sorry

/-- If every flat pullback of a family of `r`-cycles along a jointly surjective
family of flat morphisms of relative dimension `e` is a relative cycle, then
the original family is a relative cycle. -/
theorem isRelative_of_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : Family f r)
    (h : ∀ i, IsRelative (flatPullback (family i).hom e α)) :
    IsRelative α :=
  sorry

end AlgebraicGeometry.RelativeCycle
