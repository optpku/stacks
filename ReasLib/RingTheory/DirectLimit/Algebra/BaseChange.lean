module

public import ReasLib.RingTheory.DirectLimit.Algebra.Base
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change along fixed-base direct limits

This leaf owns descent statements for linear maps after base change along a
directed colimit of commutative algebras.  The stage-to-colimit transport is a
named operation, so users do not need to choose a stage algebra structure or
rebuild the iterated-base-change comparison themselves.

@stack 05LI
-/

@[expose] public section

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x y z

noncomputable section

namespace Ring.DirectLimit

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)

namespace BaseChange

/-- A linear map after base change to a stage induces a linear map after base
change to the direct limit. -/
@[stacks 05LI "direct-limit base-change stage map"]
noncomputable def stageMap [IsDirectedOrder I]
    {M : Type x} [AddCommGroup M] [Module A M]
    {N : Type y} [AddCommGroup N] [Module A N]
    (i : I) (v : R i ⊗[A] M →ₗ[R i] R i ⊗[A] N) :
    Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)) ⊗[A] M →ₗ[Ring.DirectLimit R
      (fun i j h ↦ (f i j h : R i →+* R j))]
        Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)) ⊗[A] N :=
  -- Local instance justification (stage-indexed, defeq pin): `i` determines the source algebra.
  letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) :=
    Ring.DirectLimit.Algebra.stageAlgebra (fun i j h ↦ (f i j h).toRingHom) i
  -- Local instance justification (defeq pin): base change along that stage algebra needs its tower.
  letI : IsScalarTower A (R i) (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) :=
    Ring.DirectLimit.stageAlgebra_isScalarTower R f i
  (cancelBaseChange A (R i)
      (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)))
      (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) N).toLinearMap ∘ₗ
    v.baseChange (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) ∘ₗ
    (cancelBaseChange A (R i)
      (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)))
      (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) M).symm.toLinearMap

/-- Transporting the base change of an `A`-linear map from a stage to the
direct limit recovers its direct-limit base change. -/
@[stacks 05LI "direct-limit base-change stage map"]
theorem stageMap_baseChange [IsDirectedOrder I]
    {M : Type x} [AddCommGroup M] [Module A M]
    {N : Type y} [AddCommGroup N] [Module A N]
    (i : I) (u : M →ₗ[A] N) :
    stageMap f i (u.baseChange (R i)) =
      u.baseChange (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) := sorry

/-- The stage-to-direct-limit transport preserves identity linear maps. -/
@[stacks 05LI "direct-limit base-change stage map"]
theorem stageMap_id [IsDirectedOrder I]
    {M : Type x} [AddCommGroup M] [Module A M]
    (i : I) :
    stageMap f i (LinearMap.id : R i ⊗[A] M →ₗ[R i] R i ⊗[A] M) =
      (LinearMap.id : Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)) ⊗[A] M →ₗ[Ring.DirectLimit R
        (fun i j h ↦ (f i j h : R i →+* R j))]
          Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)) ⊗[A] M) := sorry

/-- The stage-to-direct-limit transport preserves composition of linear maps. -/
@[stacks 05LI "direct-limit base-change stage map"]
theorem stageMap_comp [IsDirectedOrder I]
    {M : Type x} [AddCommGroup M] [Module A M]
    {N : Type y} [AddCommGroup N] [Module A N]
    {P : Type z} [AddCommGroup P] [Module A P]
    (i : I) (u : R i ⊗[A] M →ₗ[R i] R i ⊗[A] N)
    (v : R i ⊗[A] N →ₗ[R i] R i ⊗[A] P) :
    stageMap f i (v.comp u) = (stageMap f i v).comp (stageMap f i u) := sorry

end BaseChange

end Ring.DirectLimit
