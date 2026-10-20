module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The support of an effective relative cycle on a locally finite type morphism
over a locally Noetherian base is closed in the total space. -/
theorem isClosed_support_of_isEffective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r}
    (hα : IsRelative α) (h_eff : IsEffective α) :
    IsClosed (Scheme.Hom.CyclesOnFibers.support α) := sorry

/-- The support of a family in the effective relative-cycle submonoid is closed
in the total space over a locally Noetherian base. -/
theorem isClosed_support_of_mem_effective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r}
    (hα : α ∈ effective f r) :
    IsClosed (Scheme.Hom.CyclesOnFibers.support α) := by
  rcases (mem_effective f r α).mp hα with ⟨h_relative, h_effective⟩
  exact isClosed_support_of_isEffective h_relative h_effective

end AlgebraicGeometry.RelativeCycle
