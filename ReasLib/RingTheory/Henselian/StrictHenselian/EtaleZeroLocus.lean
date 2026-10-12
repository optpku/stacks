/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.RingHom.IndEtale.Henselian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale coordinate zero loci over strictly henselian local rings

This leaf records the coordinate form of the unique lifting principle for
etale algebras between strictly henselian local rings.

@stack 04GX
-/

@[expose] public section

universe u v

namespace StrictHenselianLocalRing

/-- Lemma 10.153.12: base change along a local map of strictly henselian local
rings bijects the coordinate zero loci of an etale polynomial presentation. -/
@[stacks 04GX "etale coordinate zero-locus bijection"]
theorem bijOn_zeroLocus_of_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [StrictHenselianLocalRing R] [StrictHenselianLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))] :
    Set.BijOn
      (fun r ↦ φ ∘ r)
      {r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0} := sorry

end StrictHenselianLocalRing
