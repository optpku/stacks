module

public import ReasLib.RingTheory.CotangentComplex.Frobenius
import StacksCheckRecall

/-!
# Frobenius functoriality of the cotangent complex

In characteristic `p`, the Section 92.6 map of `L_{B/A}` induced by the Frobenius
endomorphisms of `A` and `B` is chain-homotopic to zero.
-/

@[expose] public section

open HomologicalComplex

universe u

/- Lemma 92.10.2. -/
@[stacks 0G5Z] #check (Algebra.CotangentComplex.Frobenius.map_homotopic_zero :
  ∀ (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0),
    Nonempty (Homotopy
      (Algebra.CotangentComplex.Frobenius.map p f hp) 0))

