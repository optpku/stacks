module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Homotopy
import StacksCheckRecall

/-!
# Lemma 88.3.1

The completed naive cotangent complex of an object of (88.2.0.2) is well
defined in the homotopy category of complexes of modules.
-/

@[expose] public section

open CategoryTheory
open Algebra.NaiveCotangent.Adic

universe u

/- Lemma 88.3.1: Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `B` be an object of (88.2.0.2), i.e. an `I`-adically complete `A`-algebra
of topologically finite type. The completed naive cotangent complex
`NL_{B/A}^∧` is well defined in `K(B)`: for any two finite completed
polynomial presentations, the associated two-term complexes
`naiveCotangent I P` and `naiveCotangent I Q` are homotopy equivalent. -/
@[stacks 0GAE] #check (Algebra.NaiveCotangent.Adic.naiveCotangent_homotopyEquiv :
  ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
    {ι ι' : Type u} [Fintype ι] [Fintype ι']
    (P : Presentation A B I ι) (Q : Presentation A B I ι'),
    Nonempty (HomotopyEquiv (naiveCotangent I P) (naiveCotangent I Q)))

#check (Algebra.NaiveCotangent.Adic.naiveCotangent_iso :
  ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
    {ι ι' : Type u} [Fintype ι] [Fintype ι']
    (P : Presentation A B I ι) (Q : Presentation A B I ι'),
    Nonempty
      ((HomotopyCategory.quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (naiveCotangent I P) ≅
        (HomotopyCategory.quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (naiveCotangent I Q)))
