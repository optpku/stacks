module

public import ReasLib.RingTheory.CotangentComplex.Smooth
import StacksCheckRecall

open Algebra

universe u

/- Lemma 92.9.1. If `A → B` is a smooth ring map, then `L_{B/A} = Ω[B⁄A][0]`. -/
@[stacks 08R5] #check
  (Algebra.CotangentComplex.isIsomorphic_single_kaehler_of_smooth :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B],
    CategoryTheory.IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (ModuleCat.of B Ω[B⁄A])))

