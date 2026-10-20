/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import ReasLib.RingTheory.FiniteFree
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Monic linear factors

Reusable root-factor and finite-free root-adjunction statements for monic polynomials. The
extension, root, and complementary factor in 0530 are genuinely noncanonical existence data;
finite freeness itself is recorded by the shared ring-map predicate `RingHom.FiniteFree`.

@stack 052Z
@stack 0530
-/

universe u

namespace Polynomial.Monic

variable {R : Type u} [CommRing R]

/-- Lemma 15.21.1 (052Z): a root of a monic polynomial gives a monic complementary
factor. -/
@[stacks 052Z "monic complementary factor at a root"]
theorem exists_eq_X_sub_C_mul_of_isRoot {p : R[X]} (hp : p.Monic) {a : R}
    (ha : p.IsRoot a) :
    ∃ q : R[X], q.Monic ∧ p = (X - C a) * q := sorry
-- Proof strategy: take `q = p /ₘ (X - C a)`, use
-- `Polynomial.mul_divByMonic_eq_iff_isRoot`, and recover monicity with
-- `Polynomial.Monic.of_mul_monic_left`.

/-- Lemma 15.21.2 (0530): every monic polynomial acquires a monic linear factor after a
finite free extension of its coefficient ring. -/
@[stacks 0530 "monic linear factor after finite free extension"]
theorem exists_finiteFree_extension_with_monic_linearFactor {p : R[X]} (hp : p.Monic) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (a : S) (q : S[X]),
      (algebraMap R S).FiniteFree ∧ q.Monic ∧
        p.map (algebraMap R S) = (X - C a) * q := sorry
-- Proof strategy: take `S = AdjoinRoot p` and `a = AdjoinRoot.root p`, install
-- `hp.finite_adjoinRoot` and `hp.free_adjoinRoot`, package them through
-- `RingHom.finiteFree_algebraMap`, then apply `exists_eq_X_sub_C_mul_of_isRoot` to
-- `AdjoinRoot.isRoot_root p`.

end Polynomial.Monic
