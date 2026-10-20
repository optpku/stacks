module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.BaseChange
import StacksCheckRecall

/-!
# Lemma 88.3.4

Completed base change induces an isomorphism on degree-zero homology and a
surjection on degree-one homology of the completed naive cotangent complex.
-/

universe u

open Algebra.NaiveCotangent.Adic

/- Lemma 88.3.4 (1): The canonical completed base-change comparison induces
an isomorphism on `H^0`. -/
@[stacks 0GAG] #check (Algebra.NaiveCotangent.Adic.homologyZero_bijective :
    ∀ {A1 A2 B1 ι : Type u}
      [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
      [IsNoetherianRing A1] [IsNoetherianRing A2]
      (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
      (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
      [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
      (P : Presentation A1 B1 I1 ι),
      Function.Bijective (BaseChange.homologyZero I1 I2 hc hI hI2 P))

/- Lemma 88.3.4 (2): The same comparison induces a surjection on `H^{-1}`. -/
@[stacks 0GAG] #check (Algebra.NaiveCotangent.Adic.homologyOne_surjective :
    ∀ {A1 A2 B1 ι : Type u}
      [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
      [IsNoetherianRing A1] [IsNoetherianRing A2]
      (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
      (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
      [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
      (P : Presentation A1 B1 I1 ι),
      Function.Surjective (BaseChange.homologyOne I1 I2 hc hI hI2 P))
