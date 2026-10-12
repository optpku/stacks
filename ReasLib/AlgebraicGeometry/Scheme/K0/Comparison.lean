/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.Scheme.K0
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0

@[expose] public section

open CategoryTheory
open DerivedCategory.Bounded.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

/-- The property-indexed coherent Grothendieck relations are killed by the canonical
map to the abelian Grothendieck group of coherent modules. -/
theorem relations_le_ker_toAbelianK0 (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ≤
      (FreeAbelianGroup.lift fun F :
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory ↦
        AbelianK0.of F).ker := sorry

/-- The canonical map from the property-indexed coherent Grothendieck group to the
abelian Grothendieck group of coherent modules. -/
noncomputable def toAbelianK0 (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    K0' Y →+
      AbelianK0
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory :=
  ObjectProperty.GrothendieckGroup.lift
    (fun F ↦ AbelianK0.of F) (relations_le_ker_toAbelianK0 Y)

/-- The comparison with the abelian Grothendieck group preserves coherent-module
generators. -/
theorem toAbelianK0_of (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (F : (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory) :
    toAbelianK0 Y
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) F) =
      AbelianK0.of F := sorry

/-- The abelian Grothendieck relations of coherent modules are killed by the canonical
map to the property-indexed Grothendieck group. -/
theorem abelianRelations_le_ker_fromAbelianK0
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    AbelianK0.relations
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory ≤
      (FreeAbelianGroup.lift fun F :
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) F).ker := sorry

/-- The canonical map from the abelian Grothendieck group of coherent modules to its
property-indexed presentation. -/
noncomputable def fromAbelianK0 (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    AbelianK0
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory →+
      K0' Y :=
  AbelianK0.lift
    (fun F ↦ ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) F)
    (abelianRelations_le_ker_fromAbelianK0 Y)

/-- The map back to the property-indexed presentation preserves coherent-module
generators. -/
theorem fromAbelianK0_of (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (F : (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory) :
    fromAbelianK0 Y (AbelianK0.of F) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) F := sorry

/-- Passing from the property-indexed presentation to the abelian presentation and
back is the identity. -/
theorem from_toAbelianK0 (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    (fromAbelianK0 Y).comp (toAbelianK0 Y) = AddMonoidHom.id (K0' Y) := sorry

/-- Passing from the abelian presentation to the property-indexed presentation and
back is the identity. -/
theorem to_fromAbelianK0 (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    (toAbelianK0 Y).comp (fromAbelianK0 Y) =
      AddMonoidHom.id
        (AbelianK0
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory) := sorry

/-- The canonical additive equivalence between the two Grothendieck-group
presentations of coherent modules. -/
noncomputable def equivAbelianK0 (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    K0' Y ≃+
      AbelianK0
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory where
  toFun := toAbelianK0 Y
  invFun := fromAbelianK0 Y
  left_inv := DFunLike.congr_fun (from_toAbelianK0 Y)
  right_inv := DFunLike.congr_fun (to_fromAbelianK0 Y)
  map_add' := (toAbelianK0 Y).map_add

/-- The coherent-module comparison equivalence preserves object classes. -/
theorem equivAbelianK0_apply_of (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (F : (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory) :
    equivAbelianK0 Y
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) F) =
      AbelianK0.of F := sorry

/-- The canonical identification of `K0' Y` with the triangulated Grothendieck group
of bounded derived modules with coherent cohomology. -/
noncomputable def derivedK0Equiv (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    K0' Y ≃+
      TriangulatedK0
        (DerivedCategory.Bounded.CohomologyIn
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)) :=
  (equivAbelianK0 Y).trans
    (K0.equiv
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf))

/-- Under the derived comparison, a coherent-module class is represented by the
corresponding degree-zero bounded derived object. -/
theorem derivedK0Equiv_apply_of (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (F : (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory) :
    derivedK0Equiv Y
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) F) =
      TriangulatedK0.of
        ((Single.functor
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)).obj F) := sorry

end AlgebraicGeometry.Scheme.K0'
