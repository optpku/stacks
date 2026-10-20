/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage

/-! # Isolated singularities of morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of points of the source at which a morphism of algebraic spaces is
not smooth. -/
def nonsmoothLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points X) :=
  (Smooth.sourceLocus f).pointsSetᶜ

/-- A point lies in the nonsmooth locus if and only if the morphism is not
smooth at that point. -/
theorem mem_nonsmoothLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {x : Points X} :
    x ∈ nonsmoothLocus f ↔ ¬ SmoothAt f x :=
  sorry

/-- The nonsmooth locus is the set of points at which the morphism is not
smooth. -/
theorem nonsmoothLocus_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    nonsmoothLocus f = setOf fun x ↦ ¬ SmoothAt f x :=
  sorry

/-- The nonsmooth locus as a closed subset of the space of points of the
source. -/
def nonsmoothLocusClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Closeds (Points X) :=
  Opens.compl (Smooth.sourceLocus f).pointsOpens

/-- The carrier of `nonsmoothLocusClosed f` is `nonsmoothLocus f`. -/
theorem nonsmoothLocusClosed_carrier {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (nonsmoothLocusClosed f).carrier = nonsmoothLocus f :=
  sorry

/-- A morphism of algebraic spaces has isolated singularities if the nonsmooth
locus, endowed with its reduced induced closed subspace structure, is finite
over the target. -/
class IsolatedSingularities {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The reduced induced structure on the nonsmooth locus is finite over the
  target. -/
  isFinite_reduced :
    IsFinite ((ClosedSubspaceStructure.reduced (nonsmoothLocusClosed f)).ι ≫ f)

/-- A smooth morphism of algebraic spaces has isolated singularities. -/
instance instIsolatedSingularities_of_smooth {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f] :
    IsolatedSingularities f :=
  sorry

/-- For a proper morphism, isolated singularities is equivalent to every closed
subspace structure on the nonsmooth locus being finite over the target. -/
theorem isolatedSingularities_iff_forall {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] :
    IsolatedSingularities f ↔
      ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed f),
        IsFinite (T.ι ≫ f) :=
  sorry

/-- Isolated singularities is equivalent to some closed subspace structure on
the nonsmooth locus being finite over the target. -/
theorem isolatedSingularities_iff_exists {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsolatedSingularities f ↔
      ∃ T : ClosedSubspaceStructure (nonsmoothLocusClosed f),
        IsFinite (T.ι ≫ f) :=
  sorry

/-- `U` is a largest open of the target over which the restriction of `f` has
isolated singularities. -/
def IsLargestIsolatedSingularitiesOpen {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : OpenSubspace Y) : Prop :=
  ∀ V : OpenSubspace Y,
    IsolatedSingularities (restrictTo f V) ↔
      ∃ χ : V.X ⟶ U.X, χ ≫ U.ι = V.ι

end AlgebraicGeometry.AlgebraicSpace
