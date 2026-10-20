/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Tangent
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne.Smooth

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The zero tangent vector of the residue-slice deformation category is the
isomorphism class of the trivial dual-number deformation. -/
def trivialTangent (P : Type u) [CommRing P] [Algebra k P] :
    Functor.tangentSpace (deformationForget Λ k P) :=
  tangentSpace.mk (deformationForget Λ k P) (trivialDeformationFiber Λ k P)

/-- The trivial tangent vector is the class of the trivial deformation in the
dual-number fibre. -/
theorem trivialTangent_eq (P : Type u) [CommRing P] [Algebra k P] :
    trivialTangent Λ k P =
      tangentSpace.mk (deformationForget Λ k P) (trivialDeformationFiber Λ k P) :=
  rfl

/-- Every tangent class of a smooth algebra is the class of its trivial
dual-number deformation. -/
theorem eq_trivialTangent (P : Type u) [CommRing P] [Algebra k P] [Algebra.Smooth k P]
    (x : Functor.tangentSpace (deformationForget Λ k P)) :
    x = trivialTangent Λ k P :=
  sorry

end FlatAlgebraCat
