/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian

universe u

@[expose] public section

namespace HenselianLocalRing

/-- A commutative local ring is henselian exactly when simple roots in its residue
field of monic polynomials lift to roots with the prescribed residue. -/
theorem iff_monicSimpleRootLifting (R : Type u) [CommRing R] [IsLocalRing R] :
    HenselianLocalRing R ↔
      (∀ polynomial : Polynomial R, polynomial.Monic →
        ∀ residueRoot : IsLocalRing.ResidueField R,
          Polynomial.aeval residueRoot polynomial = 0 →
          Polynomial.aeval residueRoot polynomial.derivative ≠ 0 →
          ∃ root : R, polynomial.IsRoot root ∧ IsLocalRing.residue R root = residueRoot) := sorry

end HenselianLocalRing
