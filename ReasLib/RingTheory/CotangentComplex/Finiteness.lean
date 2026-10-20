/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Finiteness of cotangent-complex cohomology

Every cohomology module of the cotangent complex of a finite-type ring map from a
Noetherian ring is finite over the codomain.
-/

@[expose] public section

universe u

namespace Algebra.CotangentComplex

/-- The André-Quillen homology of a finite-type ring homomorphism from a Noetherian
source is a finite module over the codomain. -/
theorem homology_finite_ringHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) [IsNoetherianRing A] (hf : f.FiniteType) (n : ℤ) :
    Module.Finite B ((RingHom.cotangentComplex f).homology n) :=
  sorry

/-- Every cohomology module of the cotangent complex of a finite-type algebra over a
Noetherian ring is finite over the algebra. -/
instance homology_finite (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] (n : ℤ) :
    Module.Finite B ((Algebra.cotangentComplex A B).homology n) := by
  exact homology_finite_ringHom (algebraMap A B)
    (RingHom.finiteType_algebraMap.mpr inferInstance) n

end Algebra.CotangentComplex
