/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Jacobson
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.21.1: there exists a Jacobson, universally catenary, Noetherian domain `B`
with maximal ideals `m1`, `m2` such that `ringKrullDim (Localization.AtPrime m1) = 1` and
`ringKrullDim (Localization.AtPrime m2) = 2`. -/
@[stacks 0EEI] #check (IsJacobsonRing.exists_universallyCatenaryDomain_maximals_ringKrullDim_one_two :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsJacobsonRing B)
      (_ : UniversallyCatenaryRing.{u, u} B) (m1 m2 : Ideal B)
      (_ : m1.IsMaximal) (_ : m2.IsMaximal),
      ringKrullDim (Localization.AtPrime m1) = 1 ∧
        ringKrullDim (Localization.AtPrime m2) = 2)
