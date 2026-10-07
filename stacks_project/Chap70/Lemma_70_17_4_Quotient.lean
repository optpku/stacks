module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Base change of algebraic spaces along affine quotients

An algebraic space `X` over `Spec (CommRingCat.of A)` may be pulled back along
the closed immersion `Spec.quotientMap I` to an algebraic space over
`Spec (CommRingCat.of (A ⧸ I))`. An ideal is a maximal nonscheme ideal when that
base change is not a scheme, while every strictly larger ideal yields a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base change of an algebraic space `X` over `Spec (CommRingCat.of A)` along
the closed immersion `Spec.quotientMap I`. -/
def baseChangeQuotient {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) :
    AlgebraicSpace (Spec (CommRingCat.of (A ⧸ I))) :=
  baseChange (@Spec.quotientMap (CommRingCat.of A) I) X

/-- `baseChangeQuotient X I` is the base change of `X` along `Spec.quotientMap I`. -/
theorem baseChangeQuotient_eq {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) :
    baseChangeQuotient X I = baseChange (@Spec.quotientMap (CommRingCat.of A) I) X :=
  sorry

/-- An ideal `I` of `A` is a maximal nonscheme ideal for `X` if
`baseChangeQuotient X I` is not a scheme, while `baseChangeQuotient X J` is a
scheme whenever `I < J`. -/
def IsMaximalNonschemeIdeal {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) : Prop :=
  ¬ IsScheme (baseChangeQuotient X I) ∧
    ∀ J : Ideal A, I < J → IsScheme (baseChangeQuotient X J)

/-- `IsMaximalNonschemeIdeal X I` means that `baseChangeQuotient X I` is not a
scheme, while every strictly larger ideal yields a scheme. -/
theorem isMaximalNonschemeIdeal_iff {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) :
    IsMaximalNonschemeIdeal X I ↔
      ¬ IsScheme (baseChangeQuotient X I) ∧
        ∀ J : Ideal A, I < J → IsScheme (baseChangeQuotient X J) :=
  sorry

/-- If `I` is a maximal nonscheme ideal for `X`, then `baseChangeQuotient X I` is
not a scheme. -/
theorem not_isScheme_baseChangeQuotient {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} {I : Ideal A}
    (hI : IsMaximalNonschemeIdeal X I) :
    ¬ IsScheme (baseChangeQuotient X I) :=
  sorry

/-- If `I` is a maximal nonscheme ideal for `X` and `I < J`, then
`baseChangeQuotient X J` is a scheme. -/
theorem isScheme_baseChangeQuotient_of_lt {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} {I J : Ideal A}
    (hI : IsMaximalNonschemeIdeal X I) (hIJ : I < J) :
    IsScheme (baseChangeQuotient X J) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
