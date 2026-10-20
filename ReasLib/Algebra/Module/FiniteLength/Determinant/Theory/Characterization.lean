/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Theory

/-!
# Characterization of finite-length determinant theories
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant.Theory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A determinant theory satisfying naturality, signed three-by-three coherence, and
compatibility with a chosen usual-determinant normalization on modules annihilated by the
maximal ideal is compatibly isomorphic to the canonical determinant theory, extending that
normalization. -/
theorem characterized (D : Theory.{u, v} R) (hNatural : D.IsNatural)
    (hCoherent : D.IsCoherent)
    (e : D.restriction ≅ (canonical R).restriction)
    (hResidue : D.AgreesOnResidue e) :
    ∃ Φ : Iso D (canonical R), Φ.restrict = e := sorry

end Module.FiniteLengthDeterminant.Theory
