module

public import ReasLib.AlgebraicGeometry.RelativeCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The fibrewise equalizer of two families of `r`-cycles is the set of base
points at which their cycles on the scheme-theoretic fibre agree. -/
def eqLocus {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α β : f.FiberCycleFamily r) : Set S :=
  {s | α s = β s}

/-- A base point lies in the fibrewise equalizer if and only if the two families
agree on its scheme-theoretic fibre. -/
theorem mem_eqLocus {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    {α β : f.FiberCycleFamily r} {s : S} :
    s ∈ eqLocus α β ↔ α s = β s := sorry

/-- The fibrewise equalizer is the set of base points where the fibre cycles agree. -/
theorem eqLocus_def {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α β : f.FiberCycleFamily r) : eqLocus α β = {s | α s = β s} := sorry

/-- The fibrewise equalizer of two cycle families is the vanishing locus of their difference. -/
theorem eqLocus_sub {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α β : f.FiberCycleFamily r) : eqLocus α β = eqLocus (α - β) 0 := sorry

/-- The fibrewise equalizer of two relative `r`-cycles on a locally finite type
morphism over a locally Noetherian base is closed in the base. -/
theorem isClosed_eqLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α β : f.FiberCycleFamily r} (hα : IsRelative α) (hβ : IsRelative β) :
    IsClosed (eqLocus α β) := sorry

end AlgebraicGeometry.RelativeCycle
