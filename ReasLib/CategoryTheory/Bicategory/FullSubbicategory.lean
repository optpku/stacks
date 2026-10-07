module

public import ReasLib.CategoryTheory.Bicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Restriction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrictSlice
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans

/-!
# Induced and full subbicategories

Aggregate entry point for the reusable infrastructure formerly kept in a
single module.

New code should import the smallest fitting leaf:

* `InducedBicategory.Equivalence` for equivalence lifting along an arbitrary
  object map;
* `InducedBicategory.LocalProperties` for the forgetful local-equivalence and
  hom-groupoid instances;
* `FullSubbicategory.Definition` for an object-property subbicategory and its
  canonical inclusion;
* `FullSubbicategory.Equivalence` for the object-property-facing equivalence
  lift; or
* `FullSubbicategory.Restriction` for restricting an ordinary category
  equivalence to a full subbicategory; or
* `FullSubbicategory.Lift.Construction` for strict pseudofunctor lift construction; or
* `FullSubbicategory.Lift.Computations` for lift and inclusion readout and
  factorization API; or
* `FullSubbicategory.StrictSlice.Equivalence` for the canonical equivalence between
  internal strict slices and full subbicategories of ambient strict slices; or
* `FullSubbicategory.Pseudofunctor` for a lift of an arbitrary pseudofunctor.
* `FullSubbicategory.StrongTrans` for lifting ambient strong transformations.

`FullSubbicategory.Lift` additionally exports the local-equivalence instances
for inclusions induced by implications of object properties.
-/
