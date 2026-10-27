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
  map_one' := by
    apply U.submodule.linearMap_qext
    ext x
    change U.submodule.mkQ (CompactModule.linear Λ (M.obj.ρ 1) x) = U.submodule.mkQ x
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    apply U.submodule.linearMap_qext
    ext x
    change U.submodule.mkQ (CompactModule.linear Λ (M.obj.ρ (g * h)) x) =
      U.submodule.mkQ (CompactModule.linear Λ (M.obj.ρ g)
        (CompactModule.linear Λ (M.obj.ρ h) x))
    rw [map_mul]
    rfl

/-- The WHOLE kernel is open here because this coefficient quotient is finite.
No such assertion is made for an arbitrary infinite discrete module. -/
def normalKernel (U : OpenInvariantSubmodule Λ G M) : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup :=
        { carrier := {g | representation U g = 1}
          mul_mem' := (representation U).ker.mul_mem
          one_mem' := (representation U).ker.one_mem
          inv_mem' := (representation U).ker.inv_mem }
      isOpen' := by
        letI : Finite (quotient U) :=
          AddSubgroup.quotient_finite_of_isOpen U.submodule.toAddSubgroup U.isOpen
        have hfix (x : quotient U) : IsOpen {g : G | representation U g x = x} := by
          obtain ⟨m, rfl⟩ := U.submodule.mkQ_surjective x
          have hc : Continuous (fun g : G ↦ CompactModule.linear Λ (M.obj.ρ g) m - m) :=
            (M.property.comp (continuous_id.prodMk continuous_const)).sub continuous_const
          convert U.isOpen.preimage hc using 1
          ext g
          exact Submodule.Quotient.eq U.submodule
        have hker : {g : G | representation U g = 1} =
            ⋂ x : quotient U, {g : G | representation U g x = x} := by
          ext g
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
          constructor
          · intro h x
            rw [h]
            rfl
          · intro h
            exact LinearMap.ext h
        rw [hker]
        exact isOpen_iInter_of_finite hfix }
  isNormal' := (representation U).normal_ker

/-- Finite group quotient through which the actual stage action factors. -/
def quotientRepresentation (U : OpenInvariantSubmodule Λ G M) :
    G ⧸ (normalKernel U).toSubgroup →* Module.End Λ (quotient U) :=
  QuotientGroup.lift (normalKernel U).toSubgroup (representation U) (by
    intro g hg
    exact hg)

/-- Actual action of the finite group algebra at this stage. -/
def groupAlgebraAction (U : OpenInvariantSubmodule Λ G M) :
    MonoidAlgebra Λ (G ⧸ (normalKernel U).toSubgroup) →ₐ[Λ] Module.End Λ (quotient U) :=
  MonoidAlgebra.lift Λ (Module.End Λ (quotient U))
    (G ⧸ (normalKernel U).toSubgroup) (quotientRepresentation U)

omit [Finite Λ] [IsTopologicalGroup G] in
private theorem tensor_action_eq (U : OpenInvariantSubmodule Λ G M)
    (g : G) (a : Λ) (x : quotient U) :
    (tensorRelations U).mkQ (a ⊗ₜ[Λ] action U g x) =
      (tensorRelations U).mkQ (a ⊗ₜ[Λ] x) := by
  apply (Submodule.Quotient.eq (tensorRelations U)).2
  exact Submodule.subset_span ⟨(g, a, x), rfl⟩

/-- The displayed group-generator relations also impose balancing for every
element of the finite group algebra. The right factor Λ acts by augmentation. -/
theorem tensor_balanced (U : OpenInvariantSubmodule Λ G M)
    (r : MonoidAlgebra Λ (G ⧸ (normalKernel U).toSubgroup)) (a : Λ) (x : quotient U) :
    (tensorRelations U).mkQ (a ⊗ₜ[Λ] groupAlgebraAction U r x) =
      (tensorRelations U).mkQ
        (((r.coeff.sum fun _ c ↦ c) * a) ⊗ₜ[Λ] x) := by
  classical
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs =>
      simpa [MonoidAlgebra.coeff_add, Finsupp.sum_add_index, add_mul,
        TensorProduct.add_tmul, TensorProduct.tmul_add] using congrArg₂ (· + ·) hr hs
  | single q c =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      simpa [groupAlgebraAction, quotientRepresentation, representation,
        MonoidAlgebra.coeff_single, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_comm] using tensor_action_eq U g (c * a) x

/-- The element 1 of the RIGHT trivial module tensors with x on the LEFT. -/
def unitTensor (U : OpenInvariantSubmodule Λ G M) : quotient U →ₗ[Λ] tensorCarrier U :=
  (tensorRelations U).mkQ.comp (TensorProduct.mk Λ Λ (quotient U) 1)

theorem unitTensor_action (U : OpenInvariantSubmodule Λ G M) (g : G) (x : quotient U) :
    unitTensor U (action U g x) = unitTensor U x := by
  exact tensor_action_eq U g 1 x

end CompactRepresentation.OpenInvariantSubmodule
