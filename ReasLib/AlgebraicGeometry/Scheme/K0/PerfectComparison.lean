/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.K0.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Regular
public import ReasLib.CategoryTheory.Pretriangulated.K0.Equivalence

@[expose] public section

/-!
# Perfect and Coherent Grothendieck Groups

This module defines the canonical comparison from the triangulated Grothendieck
group of perfect complexes on a Noetherian scheme to its coherent Grothendieck
group, and records that the comparison is bijective for regular schemes.
-/

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

/-- The canonical inclusion of perfect derived `O_X`-modules into bounded derived
modules with coherent cohomology on a Noetherian scheme. -/
@[reducible]
noncomputable def perfectToBoundedCoherent (X : Scheme.{u}) [IsNoetherian X] :
    RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤
      DerivedCategory.Bounded.CohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).lift
    ((t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).lift
      RingedSpace.ModuleDerived.Perfect.ι
      (fun K ↦ (@RingedSpace.ModuleDerived.IsPerfect.boundedCoherentCohomology
        X inferInstance K.obj
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor
          X.toRingedSpace.sheaf).right K.property).2))
    (fun K ↦
      (@RingedSpace.ModuleDerived.IsPerfect.boundedCoherentCohomology
        X inferInstance K.obj
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor
          X.toRingedSpace.sheaf).right K.property).1)

/-- Forgetting boundedness and coherent cohomology from the canonical inclusion
recovers the underlying perfect derived object. -/
theorem perfectToBoundedCoherent_obj_obj (X : Scheme.{u}) [IsNoetherian X]
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    (((perfectToBoundedCoherent X).obj K).obj).obj = K.obj := sorry

/-- On a Noetherian regular scheme, the inclusion of perfect complexes into bounded
complexes with coherent cohomology is an equivalence. -/
instance perfectToBoundedCoherentIsEquivalence (X : Scheme.{u}) [IsNoetherian X]
    [Scheme.Regular X] : (perfectToBoundedCoherent X).IsEquivalence := sorry

/-- The canonical additive homomorphism from perfect-complex `K₀` to coherent-sheaf
`K₀'` on a Noetherian scheme. -/
noncomputable def toK0' (X : Scheme.{u}) [IsNoetherian X] : K0 X →+ K0' X :=
  (K0'.derivedK0Equiv X).symm.toAddMonoidHom.comp
    (TriangulatedK0.map (perfectToBoundedCoherent X))

/-- The comparison homomorphism sends a perfect-complex generator to the coherent
`K₀'` class corresponding to its bounded coherent-derived realization. -/
theorem toK0'_of (X : Scheme.{u}) [IsNoetherian X]
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    toK0' X (TriangulatedK0.of K) =
      (K0'.derivedK0Equiv X).symm
        (TriangulatedK0.of ((perfectToBoundedCoherent X).obj K)) := sorry

/-- For a Noetherian regular scheme, the canonical homomorphism from the
perfect-complex Grothendieck group to the coherent Grothendieck group is bijective. -/
theorem toK0'_bijective {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X] :
    Function.Bijective (toK0' X) := sorry

end AlgebraicGeometry.Scheme.K0
