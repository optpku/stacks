module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

/-!
# The structure sheaf in the derived quasicoherent category

The structure sheaf placed in degree zero defines a canonical object of the derived category
of modules with quasicoherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The structure sheaf placed in degree zero has quasicoherent cohomology. -/
theorem structureSheaf_mem (X : Scheme.{u}) :
    Scheme.ModuleDerived.quasicoherentProperty X
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) := sorry

/-- The structure sheaf, placed in degree zero, as a derived module with quasicoherent
cohomology. -/
noncomputable def structureSheaf (X : Scheme.{u}) :
    Scheme.ModuleDerived.Quasicoherent X :=
  ⟨(DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf),
    structureSheaf_mem X⟩

/-- The underlying derived module of the derived structure sheaf is the structure sheaf
placed in degree zero. -/
theorem structureSheaf_obj (X : Scheme.{u}) :
    (structureSheaf X).obj =
      (DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf) := sorry

/-- The derived structure sheaf is bounded below. -/
theorem structureSheaf_isBoundedBelow (X : Scheme.{u}) :
    (t.plus :
      ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
      (structureSheaf X).obj := sorry

/-- The structure sheaf in degree zero as an object of bounded-below derived
quasicoherent modules. -/
noncomputable def structureSheafPlus (X : Scheme.{u}) :
    DerivedCategory.Plus.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  ⟨⟨(structureSheaf X).obj, structureSheaf_isBoundedBelow X⟩,
    (structureSheaf X).property⟩

/-- Forgetting boundedness identifies `structureSheafPlus X` with the unbounded
derived structure sheaf. -/
noncomputable def structureSheafPlusIso (X : Scheme.{u}) :
    (DerivedCategory.Plus.CohomologyIn.toUnbounded
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj
        (structureSheafPlus X) ≅ structureSheaf X :=
  (ModuleDerived.quasicoherentProperty X).fullyFaithfulι.preimageIso
    (Iso.refl (structureSheaf X).obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
