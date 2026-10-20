module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Effective
public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom.CyclesOnFibers (Equidimensional)

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- An effective relative cycle for a locally finite-type morphism over a locally
Noetherian base is equidimensional. -/
theorem equidimensional_of_isEffective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r}
    (hα : IsRelative α) (h_eff : IsEffective α) :
    Equidimensional α := sorry

/-- Every effective relative cycle belongs to the subgroup of equidimensional
relative cycles. -/
theorem mem_equidimensional_of_mem_effective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r}
    (hα : α ∈ effective f r) :
    α ∈ equidimensional f r := by
  obtain ⟨h_rel, h_eff⟩ := (mem_effective f r α).mp hα
  exact (mem_equidimensional f r α).mpr
    ⟨h_rel, equidimensional_of_isEffective h_rel h_eff⟩

end AlgebraicGeometry.RelativeCycle
