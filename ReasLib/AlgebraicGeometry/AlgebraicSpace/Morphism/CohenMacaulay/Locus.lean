/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Cohen--Macaulay loci of morphisms of algebraic spaces

The Cohen--Macaulay locus of a flat, locally finitely presented morphism of
algebraic spaces is open and commutes with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The locus of points of `X` at which `f` is Cohen--Macaulay. -/
def cohenMacaulayLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points X) :=
  {x | CohenMacaulayAt f x}

/-- A point lies in the Cohen--Macaulay locus exactly when the morphism is
Cohen--Macaulay at that point. -/
theorem mem_cohenMacaulayLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ cohenMacaulayLocus f ↔ CohenMacaulayAt f x :=
  sorry

/-- The Cohen--Macaulay locus of a flat, locally finitely presented morphism
of algebraic spaces is open. -/
@[stacks 0E10]
theorem isOpen_cohenMacaulayLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen (cohenMacaulayLocus f) :=
  sorry

/-- The Cohen--Macaulay locus of a flat, locally finitely presented morphism
of algebraic spaces commutes with arbitrary cartesian base change. -/
@[stacks 0E10]
theorem cohenMacaulayLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] :
    cohenMacaulayLocus f' = Points.map g' ⁻¹' cohenMacaulayLocus f :=
  sorry

/-- A point of `Points X'` lies in the Cohen--Macaulay locus of `f'` if and only
if its image under `Points.map g'` lies in `cohenMacaulayLocus f`. -/
theorem mem_cohenMacaulayLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] (x' : Points X') :
    x' ∈ cohenMacaulayLocus f' ↔
      Points.map g' x' ∈ cohenMacaulayLocus f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
