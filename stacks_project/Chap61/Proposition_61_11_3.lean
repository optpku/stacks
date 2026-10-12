/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import stacks_project.Chap61.Definition_61_11_1_WContractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Proposition 61.11.3

Every commutative ring admits a faithfully flat ind-étale extension whose
target is w-contractible.
-/

@[expose] public section

universe u

namespace IsWContractibleRing

/-- Proposition 61.11.3: for every commutative ring `A` there exists a
faithfully flat, ind-étale ring map `f : A →+* D` such that `D` is
w-contractible. -/
@[stacks 0983]
theorem exists_faithfullyFlat_indEtale (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing D :=
  sorry

/-- There exists a faithfully flat ind-étale `A`-algebra whose underlying ring
is w-contractible. -/
theorem exists_faithfullyFlat_indEtale_algebra (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Module.FaithfullyFlat A D ∧ (algebraMap A D).IndEtale ∧
        IsWContractibleRing D :=
  sorry

end IsWContractibleRing
