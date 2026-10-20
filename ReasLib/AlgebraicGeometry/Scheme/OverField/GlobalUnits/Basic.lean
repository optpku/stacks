/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Units
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Finite generation of global unit quotients

This leaf records the basic geometric hypotheses that make global units modulo
base-field scalars into a finitely generated abelian group.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField.GlobalUnits

variable {k : Type u} [Field k]

/-- On a normal open subscheme of a proper variety over an algebraically closed field, global
units modulo scalar units form a finitely generated abelian group. -/
@[stacks 04L4]
theorem moduleFinite_of_normalOpen
    (X : SchemeOverField k) [IsAlgClosed k] [Variety X] [IsProper X.hom]
    (U : X.left.Opens) (hU : U.toScheme.isNormal) :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient (U.ι ≫ X.hom))) := sorry

/-- Global units modulo scalar units are finitely generated on an integral, locally algebraic
scheme over an algebraically closed field. -/
@[stacks 04L5, instance]
instance instModuleFiniteOfIntegralLocallyAlgebraic
    (X : SchemeOverField k) [IsAlgClosed k] [IsIntegral X.left] [LocallyAlgebraic X] :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

/-- Global units modulo scalar units are finitely generated on a connected, reduced locally
algebraic scheme with finitely many irreducible components over an algebraically closed field. -/
@[stacks 04L6, instance]
instance instModuleFiniteOfConnectedReduced
    (X : SchemeOverField k) [IsAlgClosed k] [ConnectedSpace X.left] [IsReduced X.left]
    [LocallyAlgebraic X] [Finite (irreducibleComponents X.left)] :
    Module.Finite ℤ (Additive (Scheme.Hom.unitsQuotient X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField.GlobalUnits
