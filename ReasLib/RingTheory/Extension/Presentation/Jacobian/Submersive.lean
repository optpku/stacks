/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import ReasLib.RingTheory.Extension.Presentation.Jacobian

/-!
# Jacobians of pre-submersive presentations

This leaf identifies mathlib's square Jacobian matrix of a pre-submersive
presentation with the corresponding row-and-column restriction of the generic
rectangular presentation Jacobian.
-/

@[expose] public section

open scoped Matrix

universe u v w t

namespace Algebra.PreSubmersivePresentation.Jacobian

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type w} {σ : Type t}

/-- Mathlib's square pre-submersive Jacobian is the transpose of the generic
presentation Jacobian restricted to the distinguished variable map. -/
@[stacks 07C8 "pre-submersive presentation Jacobian bridge"]
theorem jacobiMatrix_eq
    (P : PreSubmersivePresentation R A ι σ) [Fintype σ] [DecidableEq σ] :
    P.jacobiMatrix =
      (P.toPresentation.jacobianMatrix.submatrix (fun j ↦ j) P.map)ᵀ := sorry

end Algebra.PreSubmersivePresentation.Jacobian
