module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.BaseField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Integral

/-!
# Base-field criteria for finite global unit quotients

This leaf separates the common connected-reduced geometric hypotheses from
the alternative conditions that identify the base field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField.GlobalUnits

variable {k : Type u} [Field k]

/-- On a connected reduced locally algebraic scheme with finitely many irreducible components,
any of the standard base-field conditions implies finite generation of global units modulo
scalar units. -/
@[stacks 04L7]
theorem moduleFinite_of_baseFieldCondition
    (X : SchemeOverField k) [ConnectedSpace X.left] [IsReduced X.left]
    [LocallyAlgebraic X] [Finite (irreducibleComponents X.left)]
    (h_condition :
      BaseField.GlobalSections.isIntegrallyClosed X ∨
        BaseField.hasRationalPoint X ∨ GeometricallyIntegral X.hom) :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

namespace GlobalSections

/-- An integrally closed base field in global sections gives finite generation of global units
modulo scalar units on a variety. -/
@[stacks 04L8]
theorem moduleFinite_of_integrallyClosed
    (X : SchemeOverField k) [Variety X]
    (hX : BaseField.GlobalSections.isIntegrallyClosed X) :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

end GlobalSections

namespace FunctionField

/-- A base field algebraically closed in the function field gives finite generation of global
units modulo scalar units on a variety. -/
@[stacks 04L8]
theorem moduleFinite_of_algebraicallyClosed
    (X : SchemeOverField k) [Variety X]
    (hX : BaseField.FunctionField.isAlgebraicallyClosed X) :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

end FunctionField

/-- A geometrically integral variety has finitely generated global units modulo scalar units. -/
@[stacks 04L8, instance]
instance instModuleFiniteOfGeometricallyIntegral
    (X : SchemeOverField k) [Variety X] [GeometricallyIntegral X.hom] :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

namespace ClosedPointResidues

/-- An intersection description by closed-point residue fields gives finite generation of global
units modulo scalar units on a variety. -/
@[stacks 04L8]
theorem moduleFinite_of_intersection_eq_base
    (X : SchemeOverField k) [Variety X]
    (hX : BaseField.ClosedPointResidues.intersection_eq_base X) :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

end ClosedPointResidues

/-- Each of the four standard base-field conditions for a variety implies finite generation of
global units modulo scalar units. -/
@[stacks 04L8]
theorem moduleFinite_of_varietyBaseFieldCondition
    (X : SchemeOverField k) [Variety X]
    (h_condition :
      BaseField.GlobalSections.isIntegrallyClosed X ∨
        BaseField.FunctionField.isAlgebraicallyClosed X ∨
          GeometricallyIntegral X.hom ∨
            BaseField.ClosedPointResidues.intersection_eq_base X) :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField.GlobalUnits
