/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generation

@[expose] public section

universe u

/- Lemma 36.16.3: for a commutative ring `A`, the degree-zero derived object associated to
`𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` is a weak generator of the derived category with quasicoherent
cohomology on `ℙⁿ_A`. -/
@[stacks 0A9V] #check
  (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator_isWeakGenerator :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      CategoryTheory.IsWeakGenerator
        (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator A n))
