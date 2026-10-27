/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiberwise
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Criterion of flatness by fibres for finitely presented modules on algebraic spaces

The two flatness packages agree at points of the support, and their common locus is open
relative to the support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus where base flatness and fibrewise flatness hold together with flatness of the
intermediate space and relative flatness of the module. -/
def flatnessByFibersLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) (h : Y ⟶ Z) : Set (Points X) :=
  {x | (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt_field F f h x) ∧
      (FlatAt h (Points.map f x) ∧ flatOverAt F f x)}

/-- Membership in the common flatness locus is the conjunction of the two flatness packages. -/
theorem mem_flatnessByFibersLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    x ∈ flatnessByFibersLocus F f h ↔
      (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt_field F f h x) ∧
        (FlatAt h (Points.map f x) ∧ flatOverAt F f x) :=
  Iff.rfl

/-- For a finitely presented module on an algebraic space locally of finite presentation
over a base, and an intermediate algebraic space locally of finite type over that base,
base flatness together with fibrewise flatness at a point of the support is equivalent to
flatness of the intermediate space at the image and relative flatness of the module. -/
@[stacks 05X0]
theorem flatOverAt_and_fiber_iff_of_finitePresentation {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (x : Points X)
    (h_stalk : x ∈ moduleSupport F) :
    (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt_field F f h x) ↔
      (FlatAt h (Points.map f x) ∧ flatOverAt F f x) :=
  sorry

/-- The common flatness locus of a finitely presented module is open in its support when
the source is locally of finite presentation over the base and the intermediate space is
locally of finite type over the base. -/
@[stacks 05X0]
theorem isOpen_flatnessByFibersLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [LocallyOfFiniteType h] (F : X.Modules) [F.IsFinitePresentation] :
    IsOpen ((Subtype.val : moduleSupport F → Points X) ⁻¹'
      flatnessByFibersLocus F f h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
