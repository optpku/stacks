module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.JacobiZariski

@[expose] public section

universe u

open CategoryTheory Algebra.NaiveCotangent.Adic

/- The first map is the homology map from the termwise scalar extension. -/
#check (Algebra.NaiveCotangent.Adic.homologyOneTensor :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I C]
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (P : Presentation A B I ι) (Q : Presentation B C (I.map (algebraMap A B)) κ),
    (tensorComplex I P).homology 1 ⟶ (naiveCotangent I (Q.comp P)).homology 1)
