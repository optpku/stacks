/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Localization.Ideal
public import ReasLib.RingTheory.Localization.AtPrime.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients of prime-complement localizations

This leaf owns the map obtained by localizing an algebra homomorphism at a prime-complement and
then quotienting by the extension of an ideal of the base ring.  The construction is independent
of any chapter-specific notation; the underlying localization map remains
`AlgHom.Localization.AtPrime.map`, and the quotient map is the generic
`AlgHom.BaseIdeal.quotientMap` specialization.
-/

@[expose] public section

universe u v w

namespace AlgHom.Localization.AtPrime

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Tag `087P`: the map on prime-complement localizations after quotienting by an extended base
ideal.  The source ideal is
`Ideal.map (algebraMap R (Localization.AtPrime p)) I`, and the target ideal is the corresponding
`Ideal.map` in `Localization (Submonoid.map f.toRingHom p.primeCompl)`; the map is induced by the
localized `R`-algebra homomorphism. -/
@[stacks 087P "prime-localized quotient map by a base ideal"]
noncomputable abbrev quotientMap (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] (I : Ideal R) :
    (Localization.AtPrime p ⧸
        Ideal.map (algebraMap R (Localization.AtPrime p)) I) →ₐ[R]
      (Localization (Submonoid.map f.toRingHom p.primeCompl) ⧸
        Ideal.map (algebraMap R (Localization (Submonoid.map f.toRingHom p.primeCompl))) I) :=
  AlgHom.BaseIdeal.quotientMap (map f p) I

/-- Tag `087P`: the prime-localized quotient map sends a quotient representative to the class of
the localized image of that representative. -/
@[simp, stacks 087P "prime-localized quotient map on representatives"]
theorem quotientMap_apply_mk (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] (I : Ideal R)
    (x : Localization.AtPrime p) :
    quotientMap f p I
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R (Localization.AtPrime p)) I) x) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization (Submonoid.map f.toRingHom p.primeCompl))) I)
        (map f p x) := sorry

/-- Tag `087P`: on a localized coefficient, the prime-localized quotient map sends the class of
`algebraMap A x` to the class of `algebraMap B (f x)`. -/
@[simp, stacks 087P "prime-localized quotient map on coefficients"]
theorem quotientMap_apply_algebraMap (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] (I : Ideal R)
    (x : A) :
    quotientMap f p I
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R (Localization.AtPrime p)) I)
          (algebraMap A (Localization.AtPrime p) x)) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization (Submonoid.map f.toRingHom p.primeCompl))) I)
        (algebraMap B (Localization (Submonoid.map f.toRingHom p.primeCompl)) (f x)) := sorry

/-- Tag `087P`: bijectivity of a base-ideal quotient map is preserved by passing
to the prime-complement localization.  The statement is deliberately about
the map-level owner `AlgHom.BaseIdeal.quotientMap`; finite-presentation,
flatness, and locally-nilpotent hypotheses belong to the criteria that consume
this bridge. -/
@[stacks 087P "bijective localization of a base-ideal quotient map"]
theorem quotientMap_bijective_of_baseIdeal
    (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] (I : Ideal R)
    (hquot : Function.Bijective (AlgHom.BaseIdeal.quotientMap f I)) :
    Function.Bijective (quotientMap f p I) := sorry

end AlgHom.Localization.AtPrime
