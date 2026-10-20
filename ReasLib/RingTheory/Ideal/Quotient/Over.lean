/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fibers of quotient algebras

This leaf refines the quotient-spectrum correspondence to the primes over a
fixed base ideal.  It keeps the containment condition in the target fiber so
that quotient arguments need not repeatedly rebuild `LiesOver` witnesses.
-/

universe u v

namespace Ideal.Quotient

variable {R : Type u} {A : Type v} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Primes over a base ideal in a quotient algebra correspond to primes over the same base
ideal that contain the quotient ideal. -/
@[stacks 00UK "primes over a quotient"]
noncomputable def primesOverOrderIso (p : Ideal R) (I : Ideal A) :
    p.primesOver (A ⧸ I) ≃o {P : p.primesOver A // I ≤ P.1} where
  toFun Q :=
    ⟨(⟨Q.1.comap (Ideal.Quotient.mkₐ R I), ⟨inferInstance, inferInstance⟩⟩ :
      p.primesOver A), by
      change I ≤ Q.1.comap (Ideal.Quotient.mkₐ R I)
      exact (Ideal.Quotient.mkₐ_ker R I).symm.le.trans
        (Ideal.ker_le_comap (K := Q.1) (Ideal.Quotient.mkₐ R I))⟩
  invFun P :=
    ⟨P.1.1.map (Ideal.Quotient.mk I), ⟨
      Ideal.isPrime_map_quotientMk_of_isPrime P.2,
      by
        constructor
        rw [Ideal.under, ← Ideal.Quotient.mk_comp_algebraMap (R₁ := R) I,
          ← Ideal.comap_comap, Ideal.comap_map_mk P.2]
        exact P.1.1.over_def p⟩⟩
  left_inv Q := by
    apply Subtype.ext
    exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q.1
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact Ideal.comap_map_mk P.2
  map_rel_iff' {Q₁ Q₂} := by
    change Q₁.1.comap (Ideal.Quotient.mkₐ R I).toRingHom ≤
        Q₂.1.comap (Ideal.Quotient.mkₐ R I).toRingHom ↔ Q₁.1 ≤ Q₂.1
    rw [Ideal.Quotient.mkₐ_toRingHom]
    exact Ideal.comap_le_comap_iff_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q₁.1 Q₂.1

end Ideal.Quotient
