/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Morita.Matrix

/-!
# Morita equivalences for right modules over matrix rings

Mathlib's `ModuleCat.matrixEquivalence` is stated for left modules.  Right modules over a ring
are left modules over its opposite, so this leaf packages the resulting matrix Morita equivalence
once and exposes it at the natural right-module owner.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable (R : Type u) [Ring R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The Morita equivalence from right `R`-modules to right modules over the full matrix ring
`Matrix ι ι R`, with the chosen index `i` used by the inverse functor.

It is the standard left-module matrix equivalence over `Rᵐᵒᵖ`, transported along
`RingEquiv.mopMatrix`. -/
@[simps!]
noncomputable def matrixRightEquivalence (i : ι) :
    ModuleCat Rᵐᵒᵖ ≌ ModuleCat (Matrix ι ι R)ᵐᵒᵖ :=
  (matrixEquivalence Rᵐᵒᵖ i).trans
    (restrictScalarsEquivalenceOfRingEquiv RingEquiv.mopMatrix).symm

end ModuleCat
