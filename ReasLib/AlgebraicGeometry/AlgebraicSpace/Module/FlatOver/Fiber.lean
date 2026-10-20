/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber

/-!
# Openness of the relative flat locus in a set-theoretic fibre

For a locally finite-type morphism of algebraic spaces and a finite-type
quasi-coherent module on the source, the locus of points of a set-theoretic
fibre at which the module is flat over the target is open in that fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus in the set-theoretic fibre `fiberOver f y` at which `ℱ` is
flat over `Y`. -/
def fiberFlatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (ℱ : X.Modules) (f : X ⟶ Y) (y : Points Y) : Set (fiberOver f y) :=
  {x | flatOverAt ℱ f x.val}

/-- Membership in `fiberFlatOverLocus ℱ f y` is pointwise relative flatness of
`ℱ` over `Y` at the underlying point of `X`. -/
theorem mem_fiberFlatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (ℱ : X.Modules) (f : X ⟶ Y) (y : Points Y) (x : fiberOver f y) :
    x ∈ fiberFlatOverLocus ℱ f y ↔ flatOverAt ℱ f x.val :=
  Iff.rfl

/-- For a locally finite-type morphism and a finite-type quasicoherent module,
the relative-flatness locus is open in every set-theoretic fibre. -/
@[stacks 0CWK]
theorem isOpen_flatOverAt_fiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y) :
    IsOpen (fiberFlatOverLocus ℱ f y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
