module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Sober
public import stacks_project.Chap62.Lemma_62_6_6_Family
public import stacks_project.Chap62.Lemma_62_6_6_Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.6: if `S` is locally Noetherian and `f : X ⟶ S` is locally of finite type, then two
relative `r`-cycles on `X / S` are equal if and only if they agree on the scheme-theoretic fibre
over every generic point of an irreducible component of `S`. -/
@[stacks 0H55]
theorem eq_iff_eq_on_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {α β : Family f r} (hα : IsRelative α) (hβ : IsRelative β) :
    α = β ↔ ∀ η ∈ genericPoints S, α η = β η := sorry

/-- Agreement of relative `r`-cycles on generic points of irreducible components implies equality
of the families. -/
theorem eq_of_eq_on_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {α β : Family f r} (hα : IsRelative α) (hβ : IsRelative β)
    (h : ∀ η ∈ genericPoints S, α η = β η) : α = β := sorry

/-- Equal relative `r`-cycles agree on the fibre over every generic point of an irreducible
component. -/
theorem eq_on_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {α β : Family f r} (hα : IsRelative α) (hβ : IsRelative β)
    (h : α = β) : ∀ η ∈ genericPoints S, α η = β η := sorry

end AlgebraicGeometry.RelativeCycle
