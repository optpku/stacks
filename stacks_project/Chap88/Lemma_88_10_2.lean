module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Algebraization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 88.10.2: Let `A` be a Noetherian ring and `I ⊂ A` an ideal. Let `B`
be an object of (88.2.0.2) which is rig-étale over `(A, I)`. Then there
exists a finite type `A`-algebra `C` and an `A`-algebra isomorphism
`B ≃ₐ[A] C^∧`, where `C^∧` is `AdicCompletion (I.map (algebraMap A C)) C`. -/
@[stacks 0AKA] #check (Algebra.RigEtale.exists_finiteTypeAlgEquiv :
    ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
      (I : Ideal A) [Algebra.RigEtale I B],
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B))
