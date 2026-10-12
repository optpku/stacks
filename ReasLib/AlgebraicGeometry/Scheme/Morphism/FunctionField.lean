/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Function-field maps of scheme morphisms

This leaf owns the map on function fields induced by a morphism of integral
schemes once its action on generic points has been specified.  The generic-point
equality is explicit because an arbitrary scheme morphism need not be dominant.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A dominant morphism between integral schemes sends the generic point of its source to the
generic point of its target. -/
theorem map_genericPoint_eq_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := sorry

/-- The map on function fields induced by a morphism of integral schemes that sends the generic
point of its source to the generic point of its target. -/
noncomputable def functionFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (.of_eq h_generic.symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

/-- The function-field map is the generic-point stalk map, transported along `h_generic`. -/
theorem functionFieldMap_def
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) :
    f.functionFieldMap h_generic =
      ((Y.presheaf.stalkCongr (.of_eq h_generic.symm)).hom ≫
        f.stalkMap (genericPoint X)).hom := sorry

/-- The function-field map induced by a composite is the composite of the induced
function-field maps. -/
theorem functionFieldMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (h_f : f (genericPoint X) = genericPoint Y)
    (h_g : g (genericPoint Y) = genericPoint Z)
    (h_fg : (f ≫ g) (genericPoint X) = genericPoint Z) :
    (f ≫ g).functionFieldMap h_fg =
      (f.functionFieldMap h_f).comp (g.functionFieldMap h_g) := sorry

/-- The algebra structure on the source function field induced by a generic-point preserving
morphism of integral schemes. -/
@[reducible]
noncomputable def functionFieldAlgebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) :
    Algebra Y.functionField X.functionField :=
  (f.functionFieldMap h_generic).toAlgebra

/-- The transcendence degree of the source function field over the target function field,
computed using the algebra structure induced by a generic-point preserving morphism. -/
noncomputable def functionFieldTrdeg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) : ℕ :=
  -- Local instance justification (instance diamond): distinct morphisms can induce competing algebra structures on the same pair of function fields.
  letI : Algebra Y.functionField X.functionField := f.functionFieldAlgebra h_generic
  Cardinal.toNat (Algebra.trdeg Y.functionField X.functionField)

/-- The algebra map of `functionFieldAlgebra` is `functionFieldMap`. -/
theorem algebraMap_functionFieldAlgebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) :
    -- Local instance justification (instance diamond): select the algebra induced by this morphism because distinct morphisms can induce competing structures.
    letI : Algebra Y.functionField X.functionField := f.functionFieldAlgebra h_generic
    algebraMap Y.functionField X.functionField = f.functionFieldMap h_generic := sorry

/-- The algebra structures on function fields induced by composable morphisms form a
scalar tower. -/
theorem functionFieldAlgebra_isScalarTower
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (h_f : f (genericPoint X) = genericPoint Y)
    (h_g : g (genericPoint Y) = genericPoint Z)
    (h_fg : (f ≫ g) (genericPoint X) = genericPoint Z) :
    -- Local instance justification (instance diamond): select the algebra induced by `g` because distinct morphisms can induce competing structures.
    letI : Algebra Z.functionField Y.functionField := g.functionFieldAlgebra h_g
    -- Local instance justification (instance diamond): select the algebra induced by `f` because distinct morphisms can induce competing structures.
    letI : Algebra Y.functionField X.functionField := f.functionFieldAlgebra h_f
    -- Local instance justification (instance diamond): select the algebra induced by `f ≫ g` because distinct morphisms can induce competing structures.
    letI : Algebra Z.functionField X.functionField := (f ≫ g).functionFieldAlgebra h_fg
    IsScalarTower Z.functionField Y.functionField X.functionField := sorry

/-- A finite dominant morphism of integral schemes induces a finite-dimensional extension of
function fields. -/
theorem finiteDimensional_functionField_of_isFinite_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsFinite f] [IsDominant f] :
    let _ : Algebra Y.functionField X.functionField :=
      f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
    FiniteDimensional Y.functionField X.functionField := sorry

end AlgebraicGeometry.Scheme.Hom
