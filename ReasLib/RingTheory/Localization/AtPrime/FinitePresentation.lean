/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Exact
public import ReasLib.LinearAlgebra.QuotientByIdeal.Flat
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.Ideal.Nakayama
public import ReasLib.RingTheory.RingHom.FinitePresentation.Algebra
public import ReasLib.RingTheory.Localization.AtPrime.Kernel
public import ReasLib.RingTheory.Localization.AtPrime.Quotient

/-!
# Finite-Presentation Localization Criterion at a Prime

This leaf owns the quotient-and-flatness criterion that turns a bijective map
after prime-complement localization and quotienting by a base ideal into
vanishing of the localized kernel, and hence into an isomorphism on a
principal-open neighbourhood.  The primitive comparison map is
`AlgHom.Localization.AtPrime.quotientMap`; no chapter-local localization
notation occurs in the public API.
-/

@[expose] public section

universe u v w

namespace AlgHom.Localization.AtPrime

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

/-- Tag `087P`: let `f : S → S'` be finitely presented and surjective over `R`.  If the map
on the prime-complement localizations modulo the extended base ideal `I` is bijective, the
localized kernel of `f` vanishes whenever the target localization is flat over `R`. -/
@[stacks 087P "prime-localized kernel vanishing from a quotient comparison"]
theorem kernel_subsingleton_of_quotientMap_bijective
    (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S) [q.IsPrime]
    (hfp : RingHom.FinitePresentation (f : S →+* S'))
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))]
    (hquot : Function.Bijective (quotientMap f q I)) :
    Subsingleton (LocalizedModule q.primeCompl (RingHom.ker (f : S →+* S'))) := sorry

/-- Tag `087P`: under the quotient-and-flatness criterion at `q`, the algebra map `f` becomes
bijective after localizing away from one element outside `q`. -/
@[stacks 087P "principal-open bijectivity from a prime-local quotient comparison"]
theorem exists_notMem_awayMap_bijective_of_quotientMap_bijective
    (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S) [q.IsPrime]
    (hfp : RingHom.FinitePresentation (f : S →+* S'))
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))]
    (hquot : Function.Bijective (quotientMap f q I)) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (Localization.awayMapₐ f g) := sorry

end AlgHom.Localization.AtPrime
