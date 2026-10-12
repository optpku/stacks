/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

/-!
# Relative and ordinary finite presentation of scheme modules

This file compares relative finite presentation of scheme modules with ordinary finite
presentation and with finite presentation of the underlying scheme morphism.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Over a locally finitely presented morphism, relative finite presentation and ordinary
finite presentation agree for a quasicoherent module. -/
theorem isFinitePresentationOver_iff_isFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] :
    F.IsFinitePresentationOver f ↔ F.IsFinitePresentation := sorry

/-- A locally finite type morphism is locally of finite presentation exactly when its
structure sheaf is of finite presentation relative to the base. -/
theorem locallyOfFinitePresentation_iff_structureSheaf_isFinitePresentationOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f ↔
      IsFinitePresentationOver (SheafOfModules.unit X.ringCatSheaf : X.Modules) f := sorry

end AlgebraicGeometry.Scheme.Modules
