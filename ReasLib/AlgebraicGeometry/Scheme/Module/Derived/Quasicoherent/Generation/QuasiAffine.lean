module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Conservative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf

/-!
# Generation on quasi-affine schemes

The structure sheaf in degree zero weakly generates the derived category of modules with
quasicoherent cohomology on a quasi-affine scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The degree-zero structure sheaf weakly generates derived modules with quasicoherent
cohomology on a quasi-affine scheme. -/
theorem structureSheaf_isWeakGenerator (X : Scheme.{u}) [X.IsQuasiAffine] :
    IsWeakGenerator (structureSheaf X) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
