/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZeroLocus

/-!
# Reduced structure sheaves on algebraic spaces

Reducedness of an algebraic space is detected by its local rings, and it
controls the global sections of the structure sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Reducedness of an algebraic space is equivalent to reducedness of all its local rings. -/
theorem isReduced_iff_localRingHas {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsReduced X ↔ ∀ x : Points X, localRingHas (fun R ↦ _root_.IsReduced R) X x := by
  sorry

/-- The ring of global sections of a reduced algebraic space is reduced. -/
instance isReduced_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsReduced X] : _root_.IsReduced (globalSectionsRing X) := by
  sorry

/-- A global section whose zero locus is the whole reduced algebraic space is zero. -/
theorem eq_zero_of_zeroLocus_eq_univ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsReduced X] (f : globalSectionsRing X) (hf : X.zeroLocus {f} = Set.univ) : f = 0 := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
