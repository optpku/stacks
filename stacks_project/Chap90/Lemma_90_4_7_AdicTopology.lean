module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Maximal-adic cofinality after quotient by an intersection

If `J` is an antitone family of ideals of a Noetherian complete local ring containing
the corresponding maximal-adic powers, then the images of `J n` on the quotient by
`⨅ i, J i` are cofinal with the maximal-adic powers of that quotient.
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsCompleteLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- For an antitone family containing the maximal-adic powers, each maximal-adic
power is absorbed into some stage of the family modulo the intersection. -/
theorem exists_le_pow_sup_iInf (J : ℕ → Ideal R) (hJ_anti : Antitone J)
    (hJ_pow : ∀ n, maximalIdeal R ^ n ≤ J n) :
    ∀ n, ∃ N, J N ≤ maximalIdeal R ^ n ⊔ ⨅ i, J i := sorry

/-- The images of `J n` on `R ⧸ ⨅ i, J i` contain, and are cofinal with, the images
of the maximal-adic powers. -/
theorem definesMaximalAdicTopology_map_iInf (J : ℕ → Ideal R) (hJ_anti : Antitone J)
    (hJ_pow : ∀ n, maximalIdeal R ^ n ≤ J n) :
    let I := ⨅ i, J i;
    (∀ n, (maximalIdeal R).map (Ideal.Quotient.mk I) ^ n ≤
        (J n).map (Ideal.Quotient.mk I)) ∧
      ∀ n, ∃ N, (J N).map (Ideal.Quotient.mk I) ≤
        (maximalIdeal R).map (Ideal.Quotient.mk I) ^ n := sorry

/-- Cofinality of the images of `J` with the images of maximal-adic powers is
equivalent to absorption of those powers into some stage modulo the intersection. -/
theorem definesMaximalAdicTopology_map_iInf_iff (J : ℕ → Ideal R)
    (hJ_anti : Antitone J) (hJ_pow : ∀ n, maximalIdeal R ^ n ≤ J n) :
    (let I := ⨅ i, J i;
      (∀ n, (maximalIdeal R).map (Ideal.Quotient.mk I) ^ n ≤
          (J n).map (Ideal.Quotient.mk I)) ∧
        ∀ n, ∃ N, (J N).map (Ideal.Quotient.mk I) ≤
          (maximalIdeal R).map (Ideal.Quotient.mk I) ^ n) ↔
      ∀ n, ∃ N, J N ≤ maximalIdeal R ^ n ⊔ ⨅ i, J i := sorry

/-- If the quotient by the intersection is local, the images of `J n` are cofinal
with the powers of its maximal ideal. -/
theorem definesMaximalAdicTopology_quotient (J : ℕ → Ideal R) (hJ_anti : Antitone J)
    (hJ_pow : ∀ n, maximalIdeal R ^ n ≤ J n) [IsLocalRing (R ⧸ ⨅ i, J i)] :
    let I := ⨅ i, J i;
    (∀ n, maximalIdeal (R ⧸ I) ^ n ≤ (J n).map (Ideal.Quotient.mk I)) ∧
      ∀ n, ∃ N, (J N).map (Ideal.Quotient.mk I) ≤ maximalIdeal (R ⧸ I) ^ n := sorry

end IsCompleteLocalRing
