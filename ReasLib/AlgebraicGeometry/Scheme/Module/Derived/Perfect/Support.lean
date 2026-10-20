module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Topology.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.Linear

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a quasi-compact quasi-separated scheme, a morphism from a perfect derived module with
quasicoherent cohomology to one supported on the zero locus of a global section is annihilated
by a power of that section. -/
@[stacks 08EJ]
theorem exists_pow_smul_eq_zero {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : Γ(X, ⊤))
    {E E' : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)} (α : E ⟶ E')
    (hE : RingedSpace.ModuleDerived.IsPerfect E.obj)
    (hE' : RingedSpace.ModuleDerived.IsSupportedOn E'.obj (X.zeroLocus {f})) :
    ∃ n : ℕ, (f ^ n) • α = 0 := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
