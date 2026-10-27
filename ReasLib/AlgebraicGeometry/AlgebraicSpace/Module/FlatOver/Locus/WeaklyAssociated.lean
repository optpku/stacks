/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.LocallyFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Flat loci over algebraic spaces with locally finite weakly associated points

The relative flatness locus of a finite-type quasicoherent module over a locally
finitely presented morphism is open when the weakly associated points of the target
are locally finite. The restriction to this locus is finitely presented and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a locally finitely presented morphism of algebraic spaces, the relative flatness
locus of a finite-type quasicoherent module is open if the weakly associated points of
the target are locally finite. -/
@[stacks 0DLR]
theorem isOpen_flatOverAt_of_locallyFinite_weakAss
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    IsOpen {x | flatOverAt F f x} :=
  sorry

/-- The open of `|X|` on which `F` is flat over `Y`, assuming local finiteness of
the weakly associated points of `Y`. -/
def flatOverOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    Opens (Points X) :=
  ⟨flatOverLocus F f, isOpen_flatOverAt_of_locallyFinite_weakAss f F h_weakAss⟩

/-- Membership in `flatOverOpens f F h_weakAss` is pointwise relative flatness of
`F` over `Y`. -/
theorem mem_flatOverOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y))))
    (x : Points X) :
    x ∈ flatOverOpens f F h_weakAss ↔ flatOverAt F f x :=
  Iff.rfl

/-- For a locally finitely presented morphism with locally finite weakly associated
points on the target, the restriction of a finite-type quasicoherent module to its
relative flatness locus is finitely presented. -/
@[stacks 0DLR]
theorem flatOverLocus_isFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    ((pullback (OpenSubspace.fromOpens (flatOverOpens f F h_weakAss)).ι).obj F).IsFinitePresentation :=
  sorry

/-- For a locally finitely presented morphism with locally finite weakly associated
points on the target, the restriction of a finite-type quasicoherent module to its
relative flatness locus is flat over the target at every point. -/
@[stacks 0DLR]
theorem flatOverLocus_isFlatOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    ∀ x, flatOverAt ((pullback (OpenSubspace.fromOpens (flatOverOpens f F h_weakAss)).ι).obj F)
      ((OpenSubspace.fromOpens (flatOverOpens f F h_weakAss)).ι ≫ f) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
