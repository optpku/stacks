/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.RingTheory.RingHom.Local.Properties
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

universe u v

namespace Algebra.IsLocalIso

/-- A local isomorphism admits a finite principal-localization cover of its target. -/
theorem exists_finset_localization_away {R : Type u} {S : Type v}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [IsLocalIso R S] :
    ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
      ∀ g ∈ s, ∃ f : R, IsLocalization.Away f (Localization.Away g) :=
  sorry

/-- A local isomorphism of commutative rings is étale. -/
instance etale {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalIso R S] : Algebra.Etale R S :=
  sorry

/-- A local isomorphism of commutative rings induces isomorphisms on all target local rings. -/
theorem isIsoOnLocalRings {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalIso R S] : RingHom.IsIsoOnLocalRings (algebraMap R S) :=
  sorry

/-- A local isomorphism of commutative rings is finite type and quasi-finite. -/
theorem finiteType_quasiFinite {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalIso R S] : Algebra.FiniteType.QuasiFinite R S :=
  sorry

end Algebra.IsLocalIso
