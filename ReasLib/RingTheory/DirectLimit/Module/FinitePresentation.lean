/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented modules over ring direct limits

This leaf owns the descent of finitely presented modules and maps along a
directed system of commutative rings.  Stage algebra structures are selected
inside the relevant propositions, because the selected index is mathematical
data and must not become a global instance choice.

@stack 05N7
-/

@[expose] public section

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Module.FinitePresentation

variable {I : Type u} [Preorder I] [Nonempty I]
variable {R : I → Type v} [∀ i, CommRing (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)

variable [IsDirectedOrder I]
variable [DirectedSystem R (fun i j h ↦ f i j h)]

/-- A finitely presented module over a ring direct limit is the base change of
a finitely presented module over one stage. -/
@[stacks 05N7 "finitely presented module descent"]
theorem exists_stage
    {M : Type x} [AddCommGroup M] [Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M]
    [Module.FinitePresentation (Ring.DirectLimit R (fun i j h ↦ f i j h)) M] :
    ∃ (i : I) (M_i : Type v) (_ : AddCommGroup M_i) (_ : Module (R i) M_i)
      (_ : Module.FinitePresentation (R i) M_i),
      -- Local instance justification (stage-indexed, not globally registered): the witness `i` selects its map.
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      Nonempty (Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] M_i ≃ₗ[
        Ring.DirectLimit R (fun i j h ↦ f i j h)] M) := sorry

/-- A finitely presented module over a ring identified with a direct limit
also descends to one stage after restricting scalars along that identification. -/
@[stacks 05N7 "finitely presented module descent"]
theorem exists_stage_of_ringEquiv
    {S : Type y} [CommRing S]
    (e : Ring.DirectLimit R (fun i j h ↦ f i j h) ≃+* S)
    {M : Type x} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    ∃ (i : I) (M_i : Type v) (_ : AddCommGroup M_i) (_ : Module (R i) M_i)
      (_ : Module.FinitePresentation (R i) M_i),
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      letI : Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
        Module.compHom M e.toRingHom
      Nonempty (Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] M_i ≃ₗ[
        Ring.DirectLimit R (fun i j h ↦ f i j h)] M) := sorry

/-- A map between base changes of a finitely presented module to the direct
limit is induced from a map at a later stage. -/
@[stacks 05N7 "finitely presented module descent"]
theorem exists_stageMap
    (i : I)
    {M : Type x} [AddCommGroup M] [Module (R i) M] [Module.FinitePresentation (R i) M]
    {N : Type y} [AddCommGroup N] [Module (R i) N]
    (φ :
      -- Local instance justification (stage-indexed, not globally registered): `i` determines the direct-limit action.
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] M →ₗ[Ring.DirectLimit R
        (fun i j h ↦ f i j h)] Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] N) :
    ∃ (j : I) (hij : i ≤ j)
      (φ_j :
        -- Local instance justification (stage-indexed, not globally registered): `hij` determines scalar extension to `j`.
        letI : Algebra (R i) (R j) := (f i j hij).toAlgebra
        R j ⊗[R i] M →ₗ[R j] R j ⊗[R i] N),
      -- Local instance justification (stage-indexed, not globally registered): `i` determines the direct-limit action.
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      -- Local instance justification (stage-indexed, not globally registered): `hij` determines scalar extension to `j`.
      letI : Algebra (R i) (R j) := (f i j hij).toAlgebra
      -- Local instance justification (stage-indexed, not globally registered): `j` determines the direct-limit action.
      letI : Algebra (R j) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f j
      -- Local instance justification (defeq pin): these three stage actions form the canonical tower.
      letI : IsScalarTower (R i) (R j) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra_isScalarTower f hij
      (cancelBaseChange (R i) (R j) (Ring.DirectLimit R (fun i j h ↦ f i j h))
          (Ring.DirectLimit R (fun i j h ↦ f i j h)) N).toLinearMap ∘ₗ
        φ_j.baseChange (Ring.DirectLimit R (fun i j h ↦ f i j h)) ∘ₗ
          (cancelBaseChange (R i) (R j) (Ring.DirectLimit R (fun i j h ↦ f i j h))
            (Ring.DirectLimit R (fun i j h ↦ f i j h)) M).symm.toLinearMap =
        φ := sorry

/-- Equality of maps out of a finitely presented module after base change to
the direct limit is witnessed after base change to a later stage. -/
@[stacks 05N7 "finitely presented module descent"]
theorem exists_stage_eq
    (i : I)
    {M : Type x} [AddCommGroup M] [Module (R i) M] [Module.FinitePresentation (R i) M]
    {N : Type y} [AddCommGroup N] [Module (R i) N]
    (φ ψ : M →ₗ[R i] N)
    (h :
      -- Local instance justification (stage-indexed, not globally registered): `i` determines the direct-limit action.
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      φ.baseChange (Ring.DirectLimit R (fun i j h ↦ f i j h)) =
        ψ.baseChange (Ring.DirectLimit R (fun i j h ↦ f i j h))) :
    ∃ (j : I) (hij : i ≤ j),
      -- Local instance justification (stage-indexed, not globally registered): `hij` determines scalar extension to `j`.
      letI : Algebra (R i) (R j) := (f i j hij).toAlgebra
      φ.baseChange (R j) = ψ.baseChange (R j) := sorry

end Ring.DirectLimit.Module.FinitePresentation
