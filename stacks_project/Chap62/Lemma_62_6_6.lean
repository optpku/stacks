module

public import ReasLib.AlgebraicGeometry.RelativeCycle.GenericPoints
public import stacks_project.Chap62.Lemma_62_6_6_Family
public import stacks_project.Chap62.Lemma_62_6_6_Relative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.6: if `S` is locally Noetherian and `f : X ⟶ S` is locally of finite type, then two
relative `r`-cycles on `X / S` are equal if and only if they agree on the scheme-theoretic fibre
over every generic point of an irreducible component of `S`. -/
@[stacks 0H55] #check (AlgebraicGeometry.RelativeCycle.eq_iff_eq_on_genericPoints :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {α β : f.FiberCycleFamily r} (hα : IsRelative α) (hβ : IsRelative β),
    α = β ↔ ∀ η ∈ genericPoints S, α η = β η)

end AlgebraicGeometry.RelativeCycle
