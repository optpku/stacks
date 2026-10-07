module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CoherentCohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.Monotonicity
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.Multiplication

/-!
# Global generation of regular sheaves on projective space

This file relates Castelnuovo–Mumford regularity to global generation of the corresponding
canonical twist.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.IsMRegular

/-- If a coherent sheaf on projective space over a field is `m`-regular, then its canonical
`m`-twist is globally generated. -/
theorem isGloballyGenerated
    {k : Type u} [Field k] {n : ℕ} {ℱ : (ProjectiveSpace.scheme k n).Modules} [ℱ.IsCoherent]
    {m : ℤ} (hℱ : ProjectiveSpace.IsMRegular k n ℱ m) :
    SheafOfModules.IsGloballyGenerated (ProjectiveSpace.twist k n ℱ m) := sorry

end AlgebraicGeometry.ProjectiveSpace.IsMRegular
