module

public import ReasLib.RingTheory.AdicCompletion.EtaleApprox
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 88.6.4: Let A be a Noetherian G-ring, I an ideal of A, and B, C
finite type A-algebras. For any A-algebra map ψ of I-adic completions
B^∧ ⟶ C^∧ and any N ≥ 1, there exist an étale ring map C ⟶ C' inducing an
isomorphism C ⧸ IC ≃ C' ⧸ IC' and an A-algebra map φ : B ⟶ C' such that φ
and ψ agree modulo I^N into C^∧ = (C')^∧. -/
@[stacks 0AK4]
#check (AdicCompletion.EtaleApprox.exists_of_isGRing :
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsGRing A]
    [Algebra.FiniteType A B] [Algebra.FiniteType A C]
    (I : Ideal A)
    (ψ : AdicCompletion (Ideal.map (algebraMap A B) I) B →ₐ[A]
      AdicCompletion (Ideal.map (algebraMap A C) I) C)
    (N : ℕ) (_ : 1 ≤ N),
    ∃ (C' : Type (max u v w)) (_ : CommRing C') (_ : Algebra A C')
      (_ : Algebra C C') (_ : IsScalarTower A C C') (_ : Algebra.Etale C C'),
      Function.Bijective
          (AlgHom.BaseIdeal.quotientMap (IsScalarTower.toAlgHom A C C') I) ∧
        ∃ φ : B →ₐ[A] C', AdicCompletion.EtaleApprox.AgreeModExtensionPow I N ψ φ)
