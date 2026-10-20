/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Map.Surjective
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Semilinear.RestrictScalars

/-!
# Base-change morphisms over the original base ring

Coefficient change between two explicit scalar-extension models is semilinear over the
coefficient algebra map.  Restricting both models to the original base ring turns it into an
ordinary divided-power chain-DGA morphism.  This is the form used by homology descent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uR uS uT uA

namespace DividedPowerChainAlgebra.BaseChange

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {A : DividedPowerChainAlgebra.{uR, uA} R}

/-- Tag 09PQ: coefficient change between explicit base-change models, regarded as an ordinary
divided-power chain-DGA map over the original base ring. -/
@[stacks 09PQ "coefficient change over the original base ring"]
def mapOverBase (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) :
    DividedPowerChainAlgebra.Hom
      (DividedPowerChainAlgebra.restrictScalars (algebraMap R S) X.algebra)
      (DividedPowerChainAlgebra.restrictScalars (algebraMap R T) Y.algebra) :=
  (X.map sigma Y).restrictScalars sigma.comp_algebraMap

/-- The map over the original base ring acts degreewise by coefficient change. -/
@[simp]
theorem mapOverBase_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars
      (algebraMap R S) X.algebra).toChainDGAlgebra.X n) :
    X.mapOverBase sigma Y n x = X.map sigma Y n x := sorry

/-- On a natural-degree pure tensor, the map over the original base changes only the
coefficient. -/
@[simp]
theorem mapOverBase_tmul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.mapOverBase sigma Y n (X.pieceIso n (s ⊗ₜ[R] x)) =
      Y.pieceIso n (sigma s ⊗ₜ[R] x) := sorry

/-- Coefficient change over the original base ring is degreewise surjective when the coefficient
algebra homomorphism is surjective. -/
@[stacks 09PQ "surjective coefficient change over the original base"]
theorem mapOverBase_surjective
    (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (h_sigma : Function.Surjective sigma) :
    (X.mapOverBase sigma Y).Surjective := sorry

/-- Coefficient change over the original base commutes with the scalar-extension units. -/
@[simp]
theorem mapOverBase_unit_apply
    (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    X.mapOverBase sigma Y n (X.unit n x) = Y.unit n x := sorry

end DividedPowerChainAlgebra.BaseChange
