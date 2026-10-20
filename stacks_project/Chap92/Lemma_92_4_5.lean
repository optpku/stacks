module

public import ReasLib.RingTheory.CotangentComplex.HomologyZero
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 92.4.5. For a commutative ring map A → B, the canonical augmentation identifies
H⁰(L_{B/A}) with the B-module of Kähler differentials. -/
@[stacks 08QF] #check (Algebra.CotangentComplex.homologyZeroIso :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B],
    (Algebra.cotangentComplex A B).homology 0 ≅ ModuleCat.of B Ω[B⁄A])
