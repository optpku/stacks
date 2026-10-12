/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffinePlane.ExceptionalDivisor

/-!
# Compatibility names for the affine-plane blowup
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.AffinePlaneBlowup

#check (AlgebraicGeometry.AffinePlaneBlowup.hom :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AffinePlaneBlowup.scheme k ⟶
      AlgebraicGeometry.AffinePlaneBlowup.affinePlane k)

end AlgebraicGeometry.AffinePlaneBlowup

