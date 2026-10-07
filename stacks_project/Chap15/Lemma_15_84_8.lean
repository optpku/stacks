module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Perfect.Nilpotent
import StacksCheckRecall

@[expose] public section

/-!
@stack 0DJG

# Lemma 15.84.8 (Stacks `0DJG`)

Let `R' → A'` be flat and of finite presentation, let `R' → R` be surjective with
nilpotent kernel, and put `A = A' ⊗[R'] R`.  If the derived tensor base change of
`K' : D(A')` to `D(A)` is perfect relative to `R`, then `K'` is perfect relative to `R'`.

The reusable owner uses the explicit left tensor-factor homomorphism and also exposes the
symmetric iff.  Pseudo-coherence and finite Tor-dimension reflection are kept as independent
property-level APIs.  This source facade has no dependency on a Chapter 15.67 theorem and does
not rebuild a projective-model comparison.
-/

open CategoryTheory

open scoped TensorProduct Algebra.TensorProduct.Right

noncomputable section

universe u

/- Lemma 15.84.8, Stacks `0DJG`: relative perfectness descends across the stated surjective
nilpotent tensor base change. -/
@[stacks 0DJG "relative perfectness descends across a nilpotent base change"]
#check fun {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
    [Algebra R' A'] [Algebra R' R] [Module.Flat R' A'] [Algebra.FinitePresentation R' A']
    (hσ : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    {K : DerivedCategory (ModuleCat A')}
    (hK : (DerivedCategory.IsPerfectOver.Nilpotent.tensorBaseChange (R := R) K).IsPerfectOver R) =>
  (DerivedCategory.IsPerfectOver.Nilpotent.of_tensorBaseChange hσ hker hK : K.IsPerfectOver R')

/- The symmetric reusable form combines the source direction with ordinary flat base change. -/
@[stacks 0DJG "relative perfectness across a nilpotent base change"]
#check fun {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
    [Algebra R' A'] [Algebra R' R] [Module.Flat R' A'] [Algebra.FinitePresentation R' A']
    (hσ : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K : DerivedCategory (ModuleCat A')) =>
  (DerivedCategory.IsPerfectOver.Nilpotent.tensorBaseChange_iff hσ hker K :
    (DerivedCategory.IsPerfectOver.Nilpotent.tensorBaseChange (R := R) K).IsPerfectOver R ↔
      K.IsPerfectOver R')

/- The explicit derived tensor base-change object used in both statements. -/
#check @DerivedCategory.IsPerfectOver.Nilpotent.tensorBaseChange

/- The independent pseudo-coherence reflection used by the owner. -/
#check @DerivedCategory.IsPseudoCoherent.extension_iff

/- The independent finite Tor-dimension reflection used by the owner. -/
#check @DerivedCategory.HasFiniteTorDimension.extension_iff_of_surjective_of_nilpotent_ker

end
