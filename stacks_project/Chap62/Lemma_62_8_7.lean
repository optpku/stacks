module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional.Effective

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom.CyclesOnFibers (Equidimensional)

universe u

/- Lemma 62.8.7: if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then
`α` is equidimensional. -/
@[stacks 0H5X] #check (AlgebraicGeometry.RelativeCycle.equidimensional_of_isEffective :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r},
    RelativeCycle.IsRelative α → RelativeCycle.IsEffective α → Equidimensional α)

#check (AlgebraicGeometry.RelativeCycle.mem_equidimensional_of_mem_effective :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r},
    α ∈ RelativeCycle.effective f r → α ∈ RelativeCycle.equidimensional f r)
