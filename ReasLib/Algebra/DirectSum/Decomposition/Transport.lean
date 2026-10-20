/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting Internal Direct-Sum Decompositions

This leaf transports a `DirectSum.Decomposition` through a linear equivalence.  The component
family is pushed forward by `Submodule.map`, so the construction applies equally to universe
lifts, change-of-model equivalences, and equivalences arising from quotient presentations.
-/

@[expose] public section

open scoped DirectSum

universe u v w w'

namespace DirectSum.Decomposition

variable {R : Type u} [Semiring R]
variable {ι : Type v} [DecidableEq ι]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type w'} [AddCommMonoid N] [Module R N]

/-- The linear equivalence from `N` to the direct sum of the images of the components of `𝒜`
under `e`. -/
@[stacks 052N "direct-sum decomposition transport equivalence"]
def mapLinearEquiv (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (e : M ≃ₗ[R] N) :
    N ≃ₗ[R] DirectSum ι fun i ↦ (𝒜 i).map e.toLinearMap :=
  e.symm.trans
    ((DirectSum.decomposeLinearEquiv 𝒜).trans
      (DirectSum.congrLinearEquiv fun i ↦ e.submoduleMap (𝒜 i)))

/-- Transport a direct-sum decomposition along a linear equivalence, using the mapped component
family on the target.  This is an explicit construction rather than a global instance, since
the chosen equivalence is part of the input data. -/
@[reducible, stacks 052N "direct-sum decomposition transport"]
def map (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (e : M ≃ₗ[R] N) :
    DirectSum.Decomposition (fun i ↦ (𝒜 i).map e.toLinearMap) := by
  let componentMap : ∀ i, 𝒜 i →ₗ[R] (𝒜 i).map e.toLinearMap :=
    fun i ↦ (e.submoduleMap (𝒜 i)).toLinearMap
  let decomposeMap : N →ₗ[R] DirectSum ι fun i ↦ (𝒜 i).map e.toLinearMap :=
    (DirectSum.lmap fun i ↦ componentMap i).comp
      ((DirectSum.decomposeLinearEquiv 𝒜).toLinearMap.comp e.symm.toLinearMap)
  refine DirectSum.Decomposition.ofLinearMap
    (fun i ↦ (𝒜 i).map e.toLinearMap) decomposeMap ?_ ?_
  · have hcoe :
        e.symm.toLinearMap.comp
            ((DirectSum.coeLinearMap (fun i ↦ (𝒜 i).map e.toLinearMap)).comp
              (DirectSum.lmap fun i ↦ componentMap i)) =
          DirectSum.coeLinearMap 𝒜 := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      simp [componentMap, DirectSum.lof_eq_of]
    apply LinearMap.ext
    intro x
    apply e.symm.injective
    change e.symm
        (DirectSum.coeLinearMap (fun i ↦ (𝒜 i).map e.toLinearMap)
          ((DirectSum.lmap fun i ↦ componentMap i)
            ((DirectSum.decomposeLinearEquiv 𝒜) (e.symm x)))) =
      e.symm x
    calc
      e.symm
          (DirectSum.coeLinearMap (fun i ↦ (𝒜 i).map e.toLinearMap)
            ((DirectSum.lmap fun i ↦ componentMap i)
              ((DirectSum.decomposeLinearEquiv 𝒜) (e.symm x)))) =
          DirectSum.coeLinearMap 𝒜 ((DirectSum.decomposeLinearEquiv 𝒜) (e.symm x)) := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f ↦ f ((DirectSum.decomposeLinearEquiv 𝒜) (e.symm x))) hcoe
      _ = e.symm x := (DirectSum.decomposeLinearEquiv 𝒜).left_inv _
  · apply DirectSum.linearMap_ext
    intro i
    ext x
    rename_i j
    have hxmem : e.symm (x : N) ∈ 𝒜 i := by
      simpa using ((e.submoduleMap (𝒜 i)).symm x).2
    by_cases hij : i = j
    · subst hij
      simpa [decomposeMap, componentMap, DirectSum.decomposeLinearEquiv_apply,
        DirectSum.lof_eq_of] using
        congrArg e (DirectSum.decompose_of_mem_same 𝒜 hxmem)
    · have hji : j ≠ i := fun hji ↦ hij hji.symm
      simpa [decomposeMap, componentMap, DirectSum.decomposeLinearEquiv_apply,
        DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hji] using
          (DirectSum.decompose_of_mem_ne 𝒜 hxmem hij)

/-- The canonical transport equivalence sends a homogeneous source element to a direct sum whose
matching component is its image under the equivalence.  This is the primary component API: it
does not expose a proof-dependent local `DirectSum.Decomposition` instance. -/
@[simp, stacks 052N "transport equivalence component formula"]
theorem mapLinearEquiv_apply_of_mem
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (e : M ≃ₗ[R] N) {i : ι} {x : M} (hx : x ∈ 𝒜 i) :
    (((mapLinearEquiv 𝒜 e) (e x)) i : N) = e x := sorry

/-- Away from its degree, the image of a homogeneous element has zero component under the
canonical transport equivalence. -/
@[simp, stacks 052N "transport equivalence off-component formula"]
theorem mapLinearEquiv_apply_of_mem_ne
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (e : M ≃ₗ[R] N) {i j : ι} {x : M} (hx : x ∈ 𝒜 i) (hij : i ≠ j) :
    (((mapLinearEquiv 𝒜 e) (e x)) j : N) = 0 := sorry

end DirectSum.Decomposition
