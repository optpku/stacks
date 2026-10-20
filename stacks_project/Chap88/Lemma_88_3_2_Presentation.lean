module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.CompletionPresentation

/-!
# Completed polynomial presentations

The completed presentation associated with a chosen polynomial surjection.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

/- Lemma 88.3.2: The polynomial presentation induces a presentation of the adic
completion by completed evaluation. -/
#check (Algebra.NaiveCotangent.Adic.completionPresentation :
  ∀ {A B ι : Type u} [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α),
    Presentation A (algebraCompletion I B) I ι)
