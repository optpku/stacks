/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# The finite-free étale locus of a module on an algebraic space

For a finitely presented module flat over the target of a locally finitely presented
morphism, the finite-free étale locus is open and commutes with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `X` at which a module `F` is finite free in an étale
neighbourhood. -/
def finiteFreeEtaleLocus {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    Set (Points X) :=
  {x | finiteFreeEtaleAt F x}

/-- Membership in the finite-free étale locus is finite freeness in an étale
neighbourhood of the point. -/
theorem mem_finiteFreeEtaleLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (x : Points X) :
    x ∈ finiteFreeEtaleLocus F ↔ finiteFreeEtaleAt F x :=
  Iff.rfl

/-- The finite-free étale locus of a finitely presented module flat over the target
of a locally finitely presented morphism of algebraic spaces is open. -/
@[stacks 0CZT]
theorem isOpen_finiteFreeEtaleLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (h_flat : flatOver F f) : IsOpen (finiteFreeEtaleLocus F) :=
  sorry

/-- The finite-free étale locus of a finitely presented module flat over the target
of a locally finitely presented morphism commutes with arbitrary base change. -/
@[stacks 0CZT]
theorem finiteFreeEtaleLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) (g : Y' ⟶ Y) :
    finiteFreeEtaleLocus ((pullback (pullback.fst f g)).obj F) =
      Points.map (pullback.fst f g) ⁻¹' finiteFreeEtaleLocus F :=
  sorry

/-- A point of a base change belongs to the finite-free étale locus of the pulled-back
module exactly when its image belongs to the original finite-free étale locus. -/
theorem mem_finiteFreeEtaleLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) (g : Y' ⟶ Y)
    (x' : Points (Limits.pullback f g)) :
    x' ∈ finiteFreeEtaleLocus ((pullback (pullback.fst f g)).obj F) ↔
      Points.map (pullback.fst f g) x' ∈ finiteFreeEtaleLocus F := by
  rw [finiteFreeEtaleLocus_baseChange_eq_preimage f F h_flat g]
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
