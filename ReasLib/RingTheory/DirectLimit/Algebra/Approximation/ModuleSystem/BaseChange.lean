module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Core
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for directed module systems

This leaf is the neutral owner of the tensor maps and linear equivalences
attached to a directed module system.  The finite-type approximation API is a
thin compatibility layer in `Approximation.Module.BaseChange`.
-/

@[expose] public section

open scoped TensorProduct

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace ModuleSystem

/-
The algebra and restriction-of-scalars instances below are selected by the
particular transition or stage.  They are therefore kept local rather than
registered globally; these named maps are the reusable interface for callers.
-/

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- The canonical linear map obtained by base-changing a stage-module
transition along the corresponding target-ring transition. -/
@[stacks 00R1 "directed module system base change"]
noncomputable def transitionBaseChangeMap
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.target j ⊗[A.target i] A.moduleStage i →ₗ[A.target j] A.moduleStage j :=
  let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
  let _ : _root_.Module (A.target i) (A.moduleStage i) :=
    A.moduleStage_module i
  let _ : _root_.Module (A.target i) (A.moduleStage j) :=
    A.transitionModule h
  let _ : IsScalarTower (A.target i) (A.target j) (A.moduleStage j) :=
    RestrictScalars.isScalarTower (A.target i) (A.target j) (A.moduleStage j)
  (A.transitionBaseChange_spec h).equiv.toLinearMap

/-- The canonical linear map obtained by base-changing a stage module to the
limiting target ring. -/
@[stacks 00R1 "directed module system base change"]
noncomputable def finalBaseChangeMap (A : ModuleSystem f M) (i : A.index) :
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    S ⊗[A.target i] A.moduleStage i →ₗ[S] M :=
  let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
  let _ : _root_.Module (A.target i) (A.moduleStage i) :=
    A.moduleStage_module i
  let _ : _root_.Module (A.target i) M :=
    A.targetModule i
  let _ : IsScalarTower (A.target i) S M :=
    RestrictScalars.isScalarTower (A.target i) S M
  (A.finalBaseChange_spec i).equiv.toLinearMap

/-- The transition base-change map is surjective from the canonical
`IsBaseChange` specification. -/
@[stacks 00R1 "directed module system base change"]
theorem transitionBaseChangeMap_surjective
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) :
    Function.Surjective (A.transitionBaseChangeMap h) := sorry

/-- The transition base-change map is injective from the canonical
`IsBaseChange` specification. -/
@[stacks 00R1 "directed module system base change"]
theorem transitionBaseChangeMap_injective
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) :
    Function.Injective (A.transitionBaseChangeMap h) := sorry

/-- The transition base-change map is bijective, packaged from its two
component properties.  This is the canonical bridge for `LinearEquiv.ofBijective`.
-/
@[stacks 00R1 "directed module system base change"]
theorem transitionBaseChangeMap_bijective
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) :
    Function.Bijective (A.transitionBaseChangeMap h) := sorry

/-- The final base-change map is surjective from the canonical
`IsBaseChange` specification. -/
@[stacks 00R1 "directed module system base change"]
theorem finalBaseChangeMap_surjective (A : ModuleSystem f M) (i : A.index) :
    Function.Surjective (A.finalBaseChangeMap i) := sorry

/-- The final base-change map is injective from the canonical
`IsBaseChange` specification. -/
@[stacks 00R1 "directed module system base change"]
theorem finalBaseChangeMap_injective (A : ModuleSystem f M) (i : A.index) :
    Function.Injective (A.finalBaseChangeMap i) := sorry

/-- The final base-change map is bijective, packaged from its two component
properties.  This is the canonical bridge for `LinearEquiv.ofBijective`.
-/
@[stacks 00R1 "directed module system base change"]
theorem finalBaseChangeMap_bijective (A : ModuleSystem f M) (i : A.index) :
    Function.Bijective (A.finalBaseChangeMap i) := sorry

/-- The transition base-change map sends a pure tensor to the target scalar
times the transitioned module element. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem transitionBaseChangeMap_tmul
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j)
    (s : A.target j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChangeMap h (s ⊗ₜ[A.target i] m) = s • A.moduleMap h m := sorry

/-- The final base-change map sends a pure tensor to the limiting scalar times
the image of the stage-module element. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem finalBaseChangeMap_tmul
    (A : ModuleSystem f M) (i : A.index) (s : S) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    A.finalBaseChangeMap i (s ⊗ₜ[A.target i] m) = s • A.moduleToLimit i m := sorry

/-- The transition base-change map sends the canonical generator tensor to the
stage-module transition. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem transitionBaseChangeMap_one_tmul
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChangeMap h (1 ⊗ₜ[A.target i] m) = A.moduleMap h m := sorry

/-- The final base-change map sends the canonical generator tensor to the
stage-to-limit module map. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem finalBaseChangeMap_one_tmul
    (A : ModuleSystem f M) (i : A.index) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    A.finalBaseChangeMap i (1 ⊗ₜ[A.target i] m) = A.moduleToLimit i m := sorry

/-- The transition base-change map is a linear equivalence. -/
@[stacks 00R1 "directed module system base change"]
noncomputable def transitionBaseChange
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.target j ⊗[A.target i] A.moduleStage i ≃ₗ[A.target j] A.moduleStage j :=
  let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
  let _ : _root_.Module (A.target i) (A.moduleStage i) :=
    A.moduleStage_module i
  let _ : _root_.Module (A.target i) (A.moduleStage j) :=
    A.transitionModule h
  let _ : IsScalarTower (A.target i) (A.target j) (A.moduleStage j) :=
    RestrictScalars.isScalarTower (A.target i) (A.target j) (A.moduleStage j)
  (A.transitionBaseChange_spec h).equiv

/-- The final base-change map is a linear equivalence. -/
@[stacks 00R1 "directed module system base change"]
noncomputable def finalBaseChange (A : ModuleSystem f M) (i : A.index) :
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    S ⊗[A.target i] A.moduleStage i ≃ₗ[S] M :=
  let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
  let _ : _root_.Module (A.target i) (A.moduleStage i) :=
    A.moduleStage_module i
  let _ : _root_.Module (A.target i) M := A.targetModule i
  let _ : IsScalarTower (A.target i) S M :=
    RestrictScalars.isScalarTower (A.target i) S M
  (A.finalBaseChange_spec i).equiv

/-- The transition base-change equivalence has the canonical transition map as
its underlying linear map. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem transitionBaseChange_linear
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) :
    (A.transitionBaseChange h).toLinearMap = A.transitionBaseChangeMap h := sorry

/-- The final base-change equivalence has the canonical limiting map as its
underlying linear map. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem finalBaseChange_linear
    (A : ModuleSystem f M) (i : A.index) :
    (A.finalBaseChange i).toLinearMap = A.finalBaseChangeMap i := sorry

/-- The transition base-change equivalence evaluates on a pure tensor. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem transitionBaseChange_tmul
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j)
    (s : A.target j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChange h (s ⊗ₜ[A.target i] m) = s • A.moduleMap h m := sorry

/-- The final base-change equivalence evaluates on a pure tensor. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem finalBaseChange_tmul
    (A : ModuleSystem f M) (i : A.index) (s : S) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    A.finalBaseChange i (s ⊗ₜ[A.target i] m) = s • A.moduleToLimit i m := sorry

/-- The transition base-change equivalence sends the canonical generator tensor
to the stage-module transition. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem transitionBaseChange_one_tmul
    (A : ModuleSystem f M) {i j : A.index} (h : i ≤ j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChange h (1 ⊗ₜ[A.target i] m) = A.moduleMap h m := sorry

/-- The final base-change equivalence sends the canonical generator tensor to
the stage-to-limit module map. -/
@[simp, stacks 00R1 "directed module system base change"]
theorem finalBaseChange_one_tmul
    (A : ModuleSystem f M) (i : A.index) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    A.finalBaseChange i (1 ⊗ₜ[A.target i] m) = A.moduleToLimit i m := sorry

end ModuleSystem

end Ring.DirectLimit.Algebra.Approximation
