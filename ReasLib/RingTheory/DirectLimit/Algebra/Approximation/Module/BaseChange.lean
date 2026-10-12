/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Specialization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-change compatibility for finite-module approximations

The neutral owner of the tensor maps and equivalences is
`Approximation.ModuleSystem.BaseChange`.  This file preserves the historical
`Approximation.Module` names for consumers of the finite-type specialization;
the map and equivalence definitions below are thin adapters and do not define
a second base-change implementation.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Module

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Compatibility name for the generic module-system transition map. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
noncomputable abbrev transitionBaseChangeMap
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.target j ⊗[A.target i] A.moduleStage i →ₗ[A.target j] A.moduleStage j :=
  ModuleSystem.transitionBaseChangeMap A.toSystem h

/-- Compatibility name for the generic module-system final base-change map. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
noncomputable abbrev finalBaseChangeMap (A : Module f M) (i : A.index) :
    let _ : Algebra (A.target i) S := (A.toHom.targetToLimit i).toAlgebra
    S ⊗[A.target i] A.moduleStage i →ₗ[S] M :=
  ModuleSystem.finalBaseChangeMap A.toSystem i

/-- Compatibility theorem for surjectivity of the transition base-change map.
The generic theorem is the semantic owner. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChangeMap_surjective
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    Function.Surjective (A.transitionBaseChangeMap h) := sorry

/-- Compatibility theorem for injectivity of the transition base-change map. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChangeMap_injective
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    Function.Injective (A.transitionBaseChangeMap h) := sorry

/-- Compatibility theorem for bijectivity of the transition base-change map.
The generic module-system theorem is the semantic owner. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChangeMap_bijective
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    Function.Bijective (A.transitionBaseChangeMap h) := sorry

/-- Compatibility theorem for surjectivity of the final base-change map. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChangeMap_surjective (A : Module f M) (i : A.index) :
    Function.Surjective (A.finalBaseChangeMap i) := sorry

/-- Compatibility theorem for injectivity of the final base-change map. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChangeMap_injective (A : Module f M) (i : A.index) :
    Function.Injective (A.finalBaseChangeMap i) := sorry

/-- Compatibility theorem for bijectivity of the final base-change map.
The generic module-system theorem is the semantic owner. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChangeMap_bijective (A : Module f M) (i : A.index) :
    Function.Bijective (A.finalBaseChangeMap i) := sorry

/-- Compatibility theorem for the transition map on pure tensors. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChangeMap_tmul
    (A : Module f M) {i j : A.index} (h : i ≤ j)
    (s : A.target j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChangeMap h (s ⊗ₜ[A.target i] m) = s • A.moduleMap h m := sorry

/-- Compatibility theorem for the final map on pure tensors. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChangeMap_tmul
    (A : Module f M) (i : A.index) (s : S) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.toHom.targetToLimit i).toAlgebra
    A.finalBaseChangeMap i (s ⊗ₜ[A.target i] m) = s • A.moduleToLimit i m := sorry

/-- Compatibility theorem for the transition map on the generator tensor. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChangeMap_one_tmul
    (A : Module f M) {i j : A.index} (h : i ≤ j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChangeMap h (1 ⊗ₜ[A.target i] m) = A.moduleMap h m := sorry

/-- Compatibility theorem for the final map on the generator tensor. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChangeMap_one_tmul
    (A : Module f M) (i : A.index) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.toHom.targetToLimit i).toAlgebra
    A.finalBaseChangeMap i (1 ⊗ₜ[A.target i] m) = A.moduleToLimit i m := sorry

/-- Compatibility name for the generic transition base-change equivalence. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
noncomputable abbrev transitionBaseChange
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.target j ⊗[A.target i] A.moduleStage i ≃ₗ[A.target j] A.moduleStage j :=
  ModuleSystem.transitionBaseChange A.toSystem h

/-- Compatibility name for the generic final base-change equivalence. -/
@[stacks 00R1 "finite-module approximation base change compatibility"]
noncomputable abbrev finalBaseChange (A : Module f M) (i : A.index) :
    let _ : Algebra (A.target i) S := (A.toHom.targetToLimit i).toAlgebra
    S ⊗[A.target i] A.moduleStage i ≃ₗ[S] M :=
  ModuleSystem.finalBaseChange A.toSystem i

/-- Compatibility theorem identifying the transition equivalence's linear map. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChange_linear
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    (A.transitionBaseChange h).toLinearMap = A.transitionBaseChangeMap h := sorry

/-- Compatibility theorem identifying the final equivalence's linear map. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChange_linear
    (A : Module f M) (i : A.index) :
    (A.finalBaseChange i).toLinearMap = A.finalBaseChangeMap i := sorry

/-- Compatibility theorem for the transition equivalence on pure tensors. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChange_tmul
    (A : Module f M) {i j : A.index} (h : i ≤ j)
    (s : A.target j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChange h (s ⊗ₜ[A.target i] m) = s • A.moduleMap h m := sorry

/-- Compatibility theorem for the final equivalence on pure tensors. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChange_tmul
    (A : Module f M) (i : A.index) (s : S) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.toHom.targetToLimit i).toAlgebra
    A.finalBaseChange i (s ⊗ₜ[A.target i] m) = s • A.moduleToLimit i m := sorry

/-- Compatibility theorem for the transition equivalence on the generator
tensor. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem transitionBaseChange_one_tmul
    (A : Module f M) {i j : A.index} (h : i ≤ j) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    A.transitionBaseChange h (1 ⊗ₜ[A.target i] m) = A.moduleMap h m := sorry

/-- Compatibility theorem for the final equivalence on the generator tensor. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
theorem finalBaseChange_one_tmul
    (A : Module f M) (i : A.index) (m : A.moduleStage i) :
    let _ : Algebra (A.target i) S := (A.toHom.targetToLimit i).toAlgebra
    A.finalBaseChange i (1 ⊗ₜ[A.target i] m) = A.moduleToLimit i m := sorry

/-- Compatibility alias for `transitionBaseChange_linear`. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
abbrev transitionBaseChange_toLinearMap
    (A : Module f M) {i j : A.index} (h : i ≤ j) :
    (A.transitionBaseChange h).toLinearMap = A.transitionBaseChangeMap h :=
  ModuleSystem.transitionBaseChange_linear A.toSystem h

/-- Compatibility alias for `finalBaseChange_linear`. -/
@[simp, stacks 00R1 "finite-module approximation base change compatibility"]
abbrev finalBaseChange_toLinearMap
    (A : Module f M) (i : A.index) :
    (A.finalBaseChange i).toLinearMap = A.finalBaseChangeMap i :=
  ModuleSystem.finalBaseChange_linear A.toSystem i

end Module

end Ring.DirectLimit.Algebra.Approximation
