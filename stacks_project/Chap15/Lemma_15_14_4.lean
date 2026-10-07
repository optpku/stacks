module

import StacksCheckRecall
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.IntegrallyClosed

@[expose] public section

open scoped nonZeroDivisors

universe u

/- Lemma 15.14.4: if a localization at nonzerodivisors is absolutely integrally
closed and the base is integrally closed in it, then the base is absolutely
integrally closed. The reusable theorem works for every integrally closed
embedding, while this typed bridge retains the source localization hypothesis. -/
/-!
@stack 0DCP
-/
@[stacks 0DCP "Lemma 15.14.4"]
#check fun (A : Type u) [CommRing A] (M : Submonoid A) (_ : M ≤ A⁰)
    [IsIntegrallyClosedIn A (Localization M)]
    [IsAbsolutelyIntegrallyClosed (Localization M)] ↦
  (IsIntegrallyClosedIn.isAbsolutelyIntegrallyClosed (A := A)
    (B := Localization M))

/- The generalized descent theorem is reusable for arbitrary ambient algebras. -/
#check @IsIntegrallyClosedIn.isAbsolutelyIntegrallyClosed
