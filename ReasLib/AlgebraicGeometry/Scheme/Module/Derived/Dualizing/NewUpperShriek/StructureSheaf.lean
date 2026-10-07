module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Assignment
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedCoh

/-- The bounded-below derived structure sheaf has coherent cohomology on a locally
Noetherian scheme. -/
theorem structureSheafPlus_mem (X : Scheme.{u}) [IsLocallyNoetherian X] :
    DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (DerivedQCoh.structureSheafPlus X).obj := sorry

/-- The structure sheaf as a bounded-below derived object with coherent cohomology. -/
noncomputable def structureSheafPlus (X : Scheme.{u}) [IsLocallyNoetherian X] : Plus X :=
  ⟨(DerivedQCoh.structureSheafPlus X).obj, structureSheafPlus_mem X⟩

/-- Forgetting coherent cohomology identifies `structureSheafPlus X` with the derived
structure sheaf. -/
theorem structureSheafPlus_isIsomorphic (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsIsomorphic (structureSheafPlus X).obj.obj (DerivedQCoh.structureSheaf X).obj := sorry

end AlgebraicGeometry.Scheme.DerivedCoh
