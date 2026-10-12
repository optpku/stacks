/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import stacks_project.Chap88.Definition_88_20_1_Ring
public import stacks_project.Chap88.«88_2_3_2_BaseChange»

/-!
# Base change of rig-étale algebras

Lemma 88.8.6 records that completed base change as in Remark 88.2.3 preserves
rig-étaleness when the vanishing loci of the extended source ideal and the
target ideal agree.
-/

@[expose] public section

universe u

open Algebra.TopologicallyFiniteType

namespace Algebra.RigEtale

/-- Lemma 88.8.6: Let `A1 → A2` be a map of Noetherian rings. Let `Iᵢ ⊂ Aᵢ` be
an ideal such that `V(I1 A2) = V(I2)`. Let `B1` be in (88.2.0.2) for
`(A1, I1)`. Let `B2` be the completed base change `(B1 ⊗[A1] A2)^∧` as in
Remark 88.2.3. If `B1` is rig-étale over `(A1, I1)`, then `B2` is rig-étale
over `(A2, I2)`. -/
@[stacks 0GB2]
theorem of_baseChange {A1 A2 : Type u} [CommRing A1] [CommRing A2]
    [Algebra A1 A2] [IsNoetherianRing A1] [IsNoetherianRing A2]
    (I1 : Ideal A1) (I2 : Ideal A2)
    (hV : PrimeSpectrum.zeroLocus (I1.map (algebraMap A1 A2) : Set A2) =
      PrimeSpectrum.zeroLocus (I2 : Set A2))
    {B1 : Type u} [CommRing B1] [Algebra A1 B1] [RigEtale I1 B1] :
    RigEtale I2 (completedBaseChange A1 I2 B1) :=
  sorry

end Algebra.RigEtale
