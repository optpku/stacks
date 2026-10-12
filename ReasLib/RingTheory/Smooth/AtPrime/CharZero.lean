/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Kaehler.Regular
public import ReasLib.RingTheory.Smooth.AtPrime.Regularity

/-!
# Smoothness at a prime in characteristic zero

@stack 00TX
-/

@[expose] public section

universe u v

namespace Algebra.IsSmoothAt

/-- Lemma 10.140.7 (Stacks `00TX`): over a characteristic-zero field,
smoothness at a prime is equivalent to finite freeness of the localized
Kähler differentials and to regularity of the local ring. -/
@[stacks 00TX]
theorem charZero_tfae
    {k : Type u} {S : Type v} [Field k] [CharZero k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime] :
    List.TFAE
      [ Algebra.IsSmoothAt k q
      , Module.Finite (Localization.AtPrime q) Ω[Localization.AtPrime q⁄k] ∧
          Module.Free (Localization.AtPrime q) Ω[Localization.AtPrime q⁄k]
      , IsRegularLocalRing (Localization.AtPrime q)
      ] := sorry

end Algebra.IsSmoothAt
