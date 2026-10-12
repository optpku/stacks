/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DescentDatum.Canonical.Cosimplicial

@[expose] public section

open scoped TensorProduct TensorProduct.Right

universe u

/- Compatibility bridge for the canonical module descent datum. -/
#check (@Module.DescentDatum.canonical :
  (R A : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    (M : ModuleCat.{u} R) → Module.DescentDatum R A (M ⊗[R] A))
