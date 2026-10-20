module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Assignment
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- The value of new upper shriek on the coherent structure sheaf. -/
noncomputable def dualizingObject (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    RingedSpace.ModuleDerived X.obj.left.toRingedSpace :=
  ((D.map f).obj (DerivedCoh.structureSheafPlus Y.obj.left)).obj.obj

/-- The new-upper-shriek dualizing object is the underlying object of `D.map f`
applied to the coherent structure sheaf. -/
theorem dualizingObject_eq (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    D.dualizingObject f =
      ((D.map f).obj (DerivedCoh.structureSheafPlus Y.obj.left)).obj.obj := sorry

/-- The degree-zero cohomology module of the new-upper-shriek dualizing object. -/
noncomputable def dualizingModule (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) : X.obj.left.Modules :=
  RingedSpace.ModuleDerived.cohomologySheaf (D.dualizingObject f) 0

/-- The new-upper-shriek dualizing module is degree-zero cohomology of the dualizing
object. -/
theorem dualizingModule_eq (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) :
    D.dualizingModule f =
      RingedSpace.ModuleDerived.cohomologySheaf (D.dualizingObject f) 0 := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
