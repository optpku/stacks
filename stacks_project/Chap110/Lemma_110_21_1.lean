module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

universe u

namespace IsJacobsonRing

/-- Lemma 110.21.1: there exists a Jacobson, universally catenary, Noetherian domain `B`
with maximal ideals `m1`, `m2` such that `ringKrullDim (Localization.AtPrime m1) = 1` and
`ringKrullDim (Localization.AtPrime m2) = 2`. -/
@[stacks 0EEI]
theorem exists_universallyCatenaryDomain_maximals_ringKrullDim_one_two :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsJacobsonRing B)
      (_ : UniversallyCatenaryRing.{u, u} B) (m1 m2 : Ideal B)
      (_ : m1.IsMaximal) (_ : m2.IsMaximal),
      ringKrullDim (Localization.AtPrime m1) = 1 ∧
        ringKrullDim (Localization.AtPrime m2) = 2 := sorry

end IsJacobsonRing
