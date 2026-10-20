/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata.Characterization
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

/-!
# Finite-Type Nagata Algebras

This leaf records the stable Nagata-ring consequences of finite-type and
quasi-finite algebra structures.
-/

universe u v

namespace NagataRing

/-- Proposition 10.162.16, tag `0335`: a finite-type algebra over a Nagata
ring is Nagata. -/
@[stacks 0335]
theorem of_finiteType {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [NagataRing R] [Algebra.FiniteType R S] : NagataRing S := sorry

/-- Lemma 10.162.5, tag `032T`: a quasi-finite algebra over a Nagata ring is
Nagata. -/
@[stacks 032T]
theorem of_quasiFinite {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FiniteType.QuasiFinite R S) [NagataRing R] :
    NagataRing S := sorry

end NagataRing

namespace UniversallyJapaneseRing

/-- Lemma 10.162.3, tag `0351`: a ring is universally Japanese when every finite-type
domain algebra over it is `N-1`. -/
@[stacks 0351]
theorem of_forall_finiteType_isN1 {R : Type u} [CommRing R]
    (h : ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S],
      IsN1Ring S) :
    UniversallyJapaneseRing.{u, v} R := sorry

end UniversallyJapaneseRing
