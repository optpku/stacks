module

public import stacks_project.Chap62.Lemma_62_7_3

/-!
# Descent of equidimensional relative cycles along flat pullbacks

Equidimensionality of a relative `r`-cycle on `X / S` may be checked after
flat pullback along a jointly surjective family of flat morphisms of
relative dimension `e`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.7.6: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` locally
Noetherian and `f` locally of finite type. Let `r, e ≥ 0` be integers. Let `α`
be a relative `r`-cycle on `X / S`. Let `{f_i : X_i ⟶ X}` be a jointly
surjective family of flat morphisms, locally of finite type, and of relative
dimension `e`. Then `α` is equidimensional if and only if each flat pullback
`flatPullback (family i).hom e α` is equidimensional. -/
@[stacks 0H5N]
theorem isEquidimensional_iff_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : Family f r) (hα : IsRelative α) :
    Equidimensional α ↔ ∀ i, Equidimensional (flatPullback (family i).hom e α) :=
  sorry

/-- If every flat pullback of a relative `r`-cycle along a jointly surjective
family of flat morphisms of relative dimension `e` is equidimensional, then
the relative cycle is equidimensional. -/
theorem isEquidimensional_of_forall_flatPullback
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r e : ℕ} {ι : Type v} (family : ι → Over X)
    [∀ i, Flat (family i).hom] [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : Family f r) (hα : IsRelative α)
    (h : ∀ i, Equidimensional (flatPullback (family i).hom e α)) :
    Equidimensional α :=
  sorry

end AlgebraicGeometry.RelativeCycle
