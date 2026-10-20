/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.Quotient.LocallyNilpotent
public import ReasLib.RingTheory.Localization.AtPrime.FinitePresentation

/-!
# Bijectivity across locally nilpotent base ideals

This leaf owns the global map-level consequence of the prime-local quotient
criterion.  The quotient construction itself remains in `AlgHom.BaseIdeal`,
while the localization proof infrastructure stays below this consumer API.
-/

@[expose] public section

universe u v w

namespace AlgHom.BaseIdeal

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

/-- Tag `07RE`: a map of finite type into a flat finitely presented algebra is
bijective when its quotient by a locally nilpotent base ideal is bijective.
The public input uses the canonical `BaseIdeal.quotientMap`; prime-local
transport and finite-presentation bookkeeping are hidden in the owner below.
-/
@[stacks 07RE "bijectivity across a locally nilpotent base ideal"]
theorem bijective_of_quotientMap_bijective
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.Flat R S']
    (hquot : Function.Bijective (quotientMap f I)) :
    Function.Bijective f := sorry

end AlgHom.BaseIdeal
