module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower

/-!
# Support and ideal-power annihilation for algebraic-space modules

Uniform annihilation by a power of a quasi-coherent ideal is equivalent to containment of
the support of a coherent module in the corresponding closed subspace.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A coherent module on a Noetherian algebraic space is annihilated by some natural-number
power of a quasi-coherent ideal sheaf if and only if its support is contained set-theoretically
in the closed subspace defined by that ideal. -/
theorem exists_idealPowerProductSubobject_eq_bot_iff_moduleSupport_subset
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] (I : IdealSubobject X) [IsQuasiCoherent I] :
    (∃ n : ℕ, idealPowerProductSubobject I F n = ⊥) ↔
      moduleSupport F ⊆ Set.range (Points.map (subschemeι I)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
