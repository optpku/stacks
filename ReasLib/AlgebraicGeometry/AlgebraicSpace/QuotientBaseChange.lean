/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Base change of algebraic spaces along affine quotients

An algebraic space over an affine scheme can be pulled back to the spectrum of
a quotient ring. A maximal nonscheme ideal is maximal among the ideals for
which this base change is not a scheme.
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
  baseChange (Spec.quotientMap (R := CommRingCat.of A) I) X

/-- `baseChangeQuotient X I` is the base change of `X` along `Spec.quotientMap I`. -/
theorem baseChangeQuotient_eq {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) (I : Ideal A) :
    baseChangeQuotient X I =
      baseChange (Spec.quotientMap (R := CommRingCat.of A) I) X :=
  rfl

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
  Iff.rfl

/-- If `I` is a maximal nonscheme ideal for `X`, then `baseChangeQuotient X I` is
not a scheme. -/
theorem not_isScheme_baseChangeQuotient {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} {I : Ideal A}
    (hI : IsMaximalNonschemeIdeal X I) :
    ¬ IsScheme (baseChangeQuotient X I) :=
  hI.1

/-- If `I` is a maximal nonscheme ideal for `X` and `I < J`, then
`baseChangeQuotient X J` is a scheme. -/
theorem isScheme_baseChangeQuotient_of_lt {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} {I J : Ideal A}
    (hI : IsMaximalNonschemeIdeal X I) (hIJ : I < J) :
    IsScheme (baseChangeQuotient X J) :=
  hI.2 J hIJ

/-- A quasi-compact quasi-separated algebraic space over an affine scheme which
is not a scheme admits an ideal maximal among those whose quotient base change
is not a scheme. -/
theorem exists_isMaximalNonschemeIdeal {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [IsQuasiCompact X] [IsQuasiSeparated X] (hX : ¬ IsScheme X) :
    ∃ I : Ideal A, IsMaximalNonschemeIdeal X I :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
