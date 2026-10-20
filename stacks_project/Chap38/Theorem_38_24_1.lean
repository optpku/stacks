module

public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening.Corepresentability
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u w

namespace LocalAlgCat.Flattening

variable (A : Type u) (B : Type u) (M : Type w)
variable [CommRing A] [HenselianLocalRing A]
variable [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

section Finite

variable [Algebra.EssFiniteType A B] [Module.Finite B M]

/- Theorem 38.24.1: the closed-point flattening functor of a finite module over an
essentially finite type local algebra over a henselian base is corepresented by a quotient
of the base. -/
@[stacks 05PG] #check
  (LocalAlgCat.Flattening.exists_corepresentingIdeal A B M :
    ∃ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A),
      Nonempty ((functor A B M).CorepresentableBy
        (LocalAlgCat.quotient A I hI)))

/- The pointwise characterization identifies closed-point flatness with annihilation of the
corepresenting ideal. -/
#check
  (LocalAlgCat.Flattening.exists_corepresentingIdeal_spec A B M :
    ∃ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A),
      ∀ T : LocalAlgCat.{u} A,
        IsFlatAtClosedPoint A B M T ↔ I.map (algebraMap A T) = ⊥)

end Finite

/- For a fixed ideal, the categorical corepresentation is equivalent to its pointwise
annihilation criterion. -/
#check
  (LocalAlgCat.Flattening.corepresentableBy_quotient_iff A B M :
    ∀ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A),
      Nonempty ((functor A B M).CorepresentableBy
        (LocalAlgCat.quotient A I hI)) ↔
          ∀ T : LocalAlgCat.{u} A,
            IsFlatAtClosedPoint A B M T ↔ I.map (algebraMap A T) = ⊥)

section FinitePresentation

variable [Algebra.EssFinitePresentation A B] [Module.FinitePresentation B M]

/- Under finite-presentation hypotheses, the corepresenting ideal may be chosen finitely
generated. -/
#check
  (LocalAlgCat.Flattening.exists_fg_corepresentingIdeal A B M :
    ∃ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (_ : I.FG),
      Nonempty ((functor A B M).CorepresentableBy
        (LocalAlgCat.quotient A I hI)))

end FinitePresentation

end LocalAlgCat.Flattening
