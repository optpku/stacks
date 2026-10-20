/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.RingTheory.CompleteIntersection.OverField

/-!
# Unobstructed flat deformations of local complete intersections

The category of flat deformations of a local complete-intersection algebra over
the residue field is unobstructed over Artinian local bases.
-/

@[expose] public section

universe u

namespace FlatAlgebraCat

/-- Flat deformations of a local complete-intersection residue-field algebra lift
along every surjection of Artinian local base algebras. -/
instance instIsUnobstructed_deformationCategory
    (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (P : Type u) [CommRing P] [Algebra k P]
    [IsLocalCompleteIntersection k P] :
    CategoryTheory.Functor.IsUnobstructed (FlatAlgebraCat.deformationForget Λ k P) :=
  sorry

end FlatAlgebraCat
