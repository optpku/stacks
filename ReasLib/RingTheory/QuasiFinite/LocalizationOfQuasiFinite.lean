/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic

@[expose] public section

universe u

namespace Algebra

/-- An algebra is a localization of a quasi-finite algebra in the Stacks sense: it is a
localization of a finite-type quasi-finite algebra over the same base. -/
def IsLocalizationOfQuasiFinite (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra C S)
      (_ : IsScalarTower R C S) (M : Submonoid C),
    FiniteType R C ∧ QuasiFinite R C ∧ IsLocalization M S

/-- Unfolding of `Algebra.IsLocalizationOfQuasiFinite`. -/
theorem isLocalizationOfQuasiFinite_iff (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    IsLocalizationOfQuasiFinite R S ↔
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra C S)
          (_ : IsScalarTower R C S) (M : Submonoid C),
        FiniteType R C ∧ QuasiFinite R C ∧ IsLocalization M S := sorry

end Algebra

namespace RingHom

/-- A ring homomorphism is a localization of a quasi-finite ring map in the Stacks sense:
it factors as a finite-type quasi-finite algebra followed by a localization. -/
def IsLocalizationOfQuasiFinite {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.IsLocalizationOfQuasiFinite R S _ _ f.toAlgebra

/-- `RingHom.IsLocalizationOfQuasiFinite` agrees with the algebra-level predicate on
`algebraMap`. -/
theorem isLocalizationOfQuasiFinite_algebraMap_iff {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).IsLocalizationOfQuasiFinite ↔
      Algebra.IsLocalizationOfQuasiFinite R S := sorry

end RingHom
