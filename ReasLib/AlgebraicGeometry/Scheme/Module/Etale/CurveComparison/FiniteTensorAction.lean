/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompletedTrivialTensor
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

noncomputable section

universe u

namespace CompactRepresentation.OpenInvariantSubmodule

variable {Λ G : Type u} [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Cat Λ G}

/-- The descended action as an actual representation on the finite quotient. -/
def representation (U : OpenInvariantSubmodule Λ G M) : G →* Module.End Λ (quotient U) where
  toFun := action U
  map_one' := by sorry
  map_mul' := by sorry

/-- The WHOLE kernel is open here because this coefficient quotient is finite.
No such assertion is made for an arbitrary infinite discrete module. -/
def normalKernel (U : OpenInvariantSubmodule Λ G M) : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup :=
        { carrier := {g | representation U g = 1}
          mul_mem' := by sorry
          one_mem' := by sorry
          inv_mem' := by sorry }
      isOpen' := by sorry }
  isNormal' := by sorry

/-- Finite group quotient through which the actual stage action factors. -/
def quotientRepresentation (U : OpenInvariantSubmodule Λ G M) :
    G ⧸ (normalKernel U).toSubgroup →* Module.End Λ (quotient U) :=
  QuotientGroup.lift (normalKernel U).toSubgroup (representation U) (by sorry)

/-- Actual action of the finite group algebra at this stage. -/
def groupAlgebraAction (U : OpenInvariantSubmodule Λ G M) :
    MonoidAlgebra Λ (G ⧸ (normalKernel U).toSubgroup) →ₐ[Λ] Module.End Λ (quotient U) :=
  MonoidAlgebra.lift Λ (Module.End Λ (quotient U))
    (G ⧸ (normalKernel U).toSubgroup) (quotientRepresentation U)

/-- The displayed group-generator relations also impose balancing for every
element of the finite group algebra. The right factor Λ acts by augmentation. -/
theorem tensor_balanced (U : OpenInvariantSubmodule Λ G M)
    (r : MonoidAlgebra Λ (G ⧸ (normalKernel U).toSubgroup)) (a : Λ) (x : quotient U) :
    (tensorRelations U).mkQ (a ⊗ₜ[Λ] groupAlgebraAction U r x) =
      (tensorRelations U).mkQ
        (((r.coeff.sum fun _ c ↦ c) * a) ⊗ₜ[Λ] x) := by sorry

/-- The element 1 of the RIGHT trivial module tensors with x on the LEFT. -/
def unitTensor (U : OpenInvariantSubmodule Λ G M) : quotient U →ₗ[Λ] tensorCarrier U :=
  (tensorRelations U).mkQ.comp (TensorProduct.mk Λ Λ (quotient U) 1)

theorem unitTensor_action (U : OpenInvariantSubmodule Λ G M) (g : G) (x : quotient U) :
    unitTensor U (action U g x) = unitTensor U x := by sorry

end CompactRepresentation.OpenInvariantSubmodule
