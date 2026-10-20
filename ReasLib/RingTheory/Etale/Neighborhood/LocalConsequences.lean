/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Unramified.LocalRing
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local consequences of etale neighborhoods

Mathlib's `Algebra.IsEtaleAt R q` records formal etaleness of the stalk
`Localization.AtPrime q`.  A basic-open etale neighborhood additionally
supplies the finite-presentation information needed for finite residue-field
extensions.  The canonical owners remain `Algebra.IsEtaleAt` and
`Algebra.IsUnramifiedAt`; the basic-open condition is accepted directly only
at the bridge theorems that need it.

@stack 00U1
@stack 00U4
-/

universe u v

open IsLocalRing

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a finitely presented algebra, formal étaleness at a prime is equivalent to the existence
of an étale basic-open neighborhood of that prime. -/
@[stacks 00U1 "etale basic-open criterion"]
theorem isEtaleAt_iff_exists_etale_away [FinitePresentation R S] (q : PrimeSpectrum S) :
    IsEtaleAt R q.asIdeal ↔
      ∃ g : S, g ∉ q.asIdeal ∧ Etale R (Localization.Away g) := sorry

namespace IsEtaleAt

/-- An étale basic-open neighborhood of a prime makes the localization at that
prime formally étale over the base ring, without requiring `S` to be globally
finitely presented. -/
@[stacks 00U1 "formal etaleness from an etale neighborhood"]
theorem of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (h_etale_away : ∃ g : S, g ∉ q ∧ Etale R (Localization.Away g)) :
    IsEtaleAt R q := sorry

end IsEtaleAt

namespace IsUnramifiedAt

/-- An etale basic-open neighborhood makes the stalk formally unramified over
the base ring. -/
@[stacks 00U4 "unramified stalk of an etale neighborhood"]
theorem of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (h_etale_away : ∃ g : S, g ∉ q ∧ Etale R (Localization.Away g)) :
    IsUnramifiedAt R q := sorry

end IsUnramifiedAt

namespace EssFiniteType

/-- An etale basic-open neighborhood makes the stalk essentially of finite
type over the base ring. -/
@[stacks 00U4 "essentially finite type etale stalk"]
theorem atPrime_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (h_etale_away : ∃ g : S, g ∉ q ∧ Etale R (Localization.Away g)) :
    EssFiniteType R (Localization.AtPrime q) := sorry

end EssFiniteType

namespace Etale

/- The residue-field conclusions are exposed atomically, so consumers do not
  need a projection from a bundled statement when only one field is needed. -/

/-- An étale basic-open neighborhood induces a finite residue-field extension at the selected
prime. -/
@[stacks 00U4 "finite residue-field extension of an etale neighborhood"]
theorem residueField_finite_of_exists_away
    (q : Ideal S) [q.IsPrime]
    (h_etale_away : ∃ g : S, g ∉ q ∧ Etale R (Localization.Away g)) :
    letI : Algebra (q.under R).ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (q.under R) q
    Module.Finite (q.under R).ResidueField q.ResidueField := sorry

/-- An étale basic-open neighborhood induces a separable residue-field extension at the selected
prime. -/
@[stacks 00U4 "separable residue-field extension of an etale neighborhood"]
theorem residueField_isSeparable_of_exists_away
    (q : Ideal S) [q.IsPrime]
    (h_etale_away : ∃ g : S, g ∉ q ∧ Etale R (Localization.Away g)) :
    letI : Algebra (q.under R).ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (q.under R) q
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := sorry

/-- An étale basic-open neighborhood identifies the extension of the contracted prime with the
maximal ideal of its stalk. No
global finite presentation of `S` is required: the witness supplies the
needed local finiteness. -/
@[stacks 00U4 "maximal ideal at an etale neighborhood"]
theorem map_eq_maximalIdeal_of_exists_away
    (q : Ideal S) [q.IsPrime]
    (h_etale_away : ∃ g : S, g ∉ q ∧ Etale R (Localization.Away g)) :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := sorry

end Etale

namespace IsUnramifiedAt

/-- An essentially finite type unramified stalk identifies the extension of
the contracted prime with its maximal ideal. -/
@[stacks 00U4 "local maximal-ideal consequence of unramifiedness"]
theorem map_eq_maximalIdeal
    (q : Ideal S) [q.IsPrime] [IsUnramifiedAt R q]
    [EssFiniteType R (Localization.AtPrime q)] :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := sorry

/-- An essentially finite type unramified stalk has finite residue-field
extension over the contracted prime. -/
@[stacks 00U4 "finite residue field of an unramified stalk"]
theorem residueField_finite
    (q : Ideal S) [q.IsPrime] [IsUnramifiedAt R q]
    [EssFiniteType R (Localization.AtPrime q)] :
    letI : Algebra (q.under R).ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (q.under R) q
    Module.Finite (q.under R).ResidueField q.ResidueField := sorry

/-- An essentially finite type unramified stalk has separable residue-field
extension over the contracted prime. -/
@[stacks 00U4 "separable residue field of an unramified stalk"]
theorem residueField_isSeparable
    (q : Ideal S) [q.IsPrime] [IsUnramifiedAt R q]
    [EssFiniteType R (Localization.AtPrime q)] :
    letI : Algebra (q.under R).ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (q.under R) q
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := sorry

end IsUnramifiedAt

end Algebra
