module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.Noetherian

/-!
# Completions of finite type algebras in C'

The `I`-adic completion of a finite type algebra over a Noetherian ring lies
in `C'`.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

#check (Algebra.TopologicallyFiniteType.instOfFiniteType I :
  ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C],
    Algebra.TopologicallyFiniteType I (AdicCompletion (I.map (algebraMap A C)) C))

#check (CommAlgCat.TopologicallyFiniteType.ofFiniteType I :
  ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C],
    CommAlgCat.TopologicallyFiniteType.{u} A I)

#check (CommAlgCat.TopologicallyFiniteType.ofFiniteType_obj I :
  ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C],
    (CommAlgCat.TopologicallyFiniteType.ofFiniteType I C).obj =
      CommAlgCat.of A (AdicCompletion (I.map (algebraMap A C)) C))
