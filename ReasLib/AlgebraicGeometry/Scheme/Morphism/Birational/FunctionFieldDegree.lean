/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
import Mathlib.Tactic.CrossRefAttribute

/-!
# Function-Field Degrees of Scheme Morphisms

This leaf gives the numerical degree of a morphism of integral schemes once
the associated extension of function fields has been supplied.  It is kept
next to the birational infrastructure because it is the common numerical
input for generic-fibre, birational, and alteration arguments.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree of a morphism of integral schemes whose induced extension of
function fields is finite.  The `Algebra` instance is intentionally explicit:
Mathlib owns the function fields, while applications supply the particular
extension induced by the morphism. -/
noncomputable abbrev functionFieldDegree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField] : ℕ :=
  Module.finrank Y.functionField X.functionField

/-- `functionFieldDegree` is definitionally the finrank of the supplied
extension of function fields. -/
theorem functionFieldDegree_eq_finrank {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField] :
    f.functionFieldDegree = Module.finrank Y.functionField X.functionField := sorry

/-- A finite extension of function fields has positive degree. -/
theorem functionFieldDegree_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Algebra Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField] :
    0 < f.functionFieldDegree := sorry

/-- Function-field degrees multiply along a tower of finite extensions. -/
theorem functionFieldDegree_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [Algebra Y.functionField X.functionField]
    [Algebra Z.functionField Y.functionField]
    [Algebra Z.functionField X.functionField]
    [IsScalarTower Z.functionField Y.functionField X.functionField]
    [FiniteDimensional Y.functionField X.functionField]
    [FiniteDimensional Z.functionField Y.functionField] :
    -- Local instance justification (proof-local temporary data): derive the composite finite-dimensionality from the two steps solely for the degree comparison.
    letI : FiniteDimensional Z.functionField X.functionField :=
      FiniteDimensional.trans Z.functionField Y.functionField X.functionField
    (f ≫ g).functionFieldDegree = f.functionFieldDegree * g.functionFieldDegree := sorry

/-- A dominant morphism of integral schemes has a finite function-field extension when the
extension defined by its induced map on function fields is finite-dimensional. -/
def FiniteFunctionFieldExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] : Prop :=
  -- Local instance justification (instance diamond): select the algebra induced by `f` because distinct morphisms can induce competing structures.
  letI : Algebra Y.functionField X.functionField :=
    f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
  FiniteDimensional Y.functionField X.functionField

/-- Finiteness of the function-field extension induced by a dominant morphism is exactly
finite-dimensionality for its induced algebra structure. -/
theorem finiteFunctionFieldExtension_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f.FiniteFunctionFieldExtension ↔
      -- Local instance justification (instance diamond): select the algebra induced by `f` because distinct morphisms can induce competing structures.
      letI : Algebra Y.functionField X.functionField :=
        f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
      FiniteDimensional Y.functionField X.functionField := sorry

/-- Finite function-field extensions are closed under composition of dominant morphisms of
integral schemes. -/
theorem finiteFunctionFieldExtension_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsDominant f] [IsDominant g]
    (hf : f.FiniteFunctionFieldExtension)
    (hg : g.FiniteFunctionFieldExtension) :
    (f ≫ g).FiniteFunctionFieldExtension := sorry

/-- The degree of the function-field extension canonically induced by a dominant morphism of
integral schemes. -/
@[stacks 02NY]
noncomputable def inducedFunctionFieldDegree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] : ℕ :=
  -- Local instance justification (instance diamond): select the algebra induced by `f`
  -- because distinct morphisms can induce competing structures.
  letI : Algebra Y.functionField X.functionField :=
    f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
  Module.finrank Y.functionField X.functionField

/-- The degree induced by a dominant morphism is the finrank for its induced function-field
algebra structure. -/
theorem inducedFunctionFieldDegree_eq_finrank {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f.inducedFunctionFieldDegree =
      -- Local instance justification (instance diamond): select the algebra induced by `f` because distinct morphisms can induce competing structures.
      letI : Algebra Y.functionField X.functionField :=
        f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
      Module.finrank Y.functionField X.functionField := sorry

/-- A finite function-field extension induced by a dominant morphism has positive degree. -/
theorem inducedFunctionFieldDegree_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (hf : f.FiniteFunctionFieldExtension) :
    0 < f.inducedFunctionFieldDegree := sorry

/-- For dominant locally finite type morphisms of integral schemes with finite induced
function-field extensions, the degree of the composite is the product of the degrees. -/
theorem inducedFunctionFieldDegree_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [IsDominant f] [IsDominant g]
    (hf : f.FiniteFunctionFieldExtension)
    (hg : g.FiniteFunctionFieldExtension) :
    (f ≫ g).inducedFunctionFieldDegree =
      f.inducedFunctionFieldDegree * g.inducedFunctionFieldDegree := sorry

end AlgebraicGeometry.Scheme.Hom
