module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Jacobian

universe u

#check (Algebra.NaiveCotangent.Adic.Presentation.jacobianMinor :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {I : Ideal A} {ι : Type u}
    (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι) {m : ℕ}
    (fs : Fin m → P.ker) (cols : Fin m ↪ ι), B)
