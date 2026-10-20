/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Pushout.Core
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-oriented base change for directed module systems

The ring-level pushout theorem is owned by `Approximation.Pushout.Core`.
This leaf combines it with the generic module-system final base-change
equivalence, so finite-module specializations can reuse the same source-side
tensor equivalence without a second implementation.
-/

@[expose] public section

open scoped TensorProduct

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/- The source-stage scalar action and the scalar towers below are induced by
the displayed comparison maps.  They are local because those maps are part of
the system data and are not globally canonical instances. -/

/-- The source-oriented base-change equivalence obtained from the ring pushout
at a stage of a directed module system. -/
@[stacks 00R1 "directed module system source base change"]
noncomputable def baseChangeSource (A : ModuleSystem f M) (i : A.index) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.toHom.targetToLimit_isScalarTower i
    let _ : _root_.Module (A.source i) (A.moduleStage i) :=
      A.sourceModule i
    let _ : IsScalarTower (A.source i) (A.target i) (A.moduleStage i) :=
      RestrictScalars.isScalarTower (A.source i) (A.target i)
        (A.moduleStage i)
    let _ : _root_.Module R M := _root_.Module.compHom M f
    R ⊗[A.source i] A.moduleStage i ≃ₗ[R] M :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.source i) S :=
    (f.comp (A.sourceToLimit i)).toAlgebra
  let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
  let _ : IsScalarTower (A.source i) R S :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (A.source i) (A.target i) S :=
    A.toHom.targetToLimit_isScalarTower i
  let _ : _root_.Module (A.source i) (A.moduleStage i) :=
    A.sourceModule i
  let _ : IsScalarTower (A.source i) (A.target i) (A.moduleStage i) :=
    RestrictScalars.isScalarTower (A.source i) (A.target i) (A.moduleStage i)
  let _ : _root_.Module R M := _root_.Module.compHom M f
  let _ : IsScalarTower R S M := RestrictScalars.isScalarTower R S M
  let _ : Algebra.IsPushout (A.source i) R (A.target i) S :=
    A.toHom.final_isPushout A.stageBaseChange_bijective i
  let eCancel : R ⊗[A.source i] A.moduleStage i ≃ₗ[R]
      S ⊗[A.target i] A.moduleStage i :=
    (Algebra.IsPushout.cancelBaseChange (A.source i) R (A.target i) S
      (A.moduleStage i)).symm
  let eFinal : S ⊗[A.target i] A.moduleStage i ≃ₗ[R] M :=
    (A.finalBaseChange i).restrictScalars R
  eCancel.trans eFinal

/-- The source-oriented base-change equivalence sends a pure tensor to the
limiting source scalar acting through the prescribed ring homomorphism. -/
@[simp, stacks 00R1 "directed module system source base change"]
theorem baseChangeSource_tmul (A : ModuleSystem f M) (i : A.index)
    (r : R) (m : A.moduleStage i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.toHom.targetToLimit_isScalarTower i
    let _ : _root_.Module (A.source i) (A.moduleStage i) :=
      A.sourceModule i
    let _ : IsScalarTower (A.source i) (A.target i) (A.moduleStage i) :=
      RestrictScalars.isScalarTower (A.source i) (A.target i)
        (A.moduleStage i)
    let _ : _root_.Module R M := _root_.Module.compHom M f
    A.baseChangeSource i (r ⊗ₜ[A.source i] m) =
      f r • A.moduleToLimit i m := sorry

/-- The source-oriented base-change equivalence sends the canonical generator
tensor to the limiting image of the stage-module element. -/
@[simp, stacks 00R1 "directed module system source base change"]
theorem baseChangeSource_one_tmul (A : ModuleSystem f M) (i : A.index)
    (m : A.moduleStage i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.toHom.targetToLimit_isScalarTower i
    let _ : _root_.Module (A.source i) (A.moduleStage i) :=
      A.sourceModule i
    let _ : IsScalarTower (A.source i) (A.target i) (A.moduleStage i) :=
      RestrictScalars.isScalarTower (A.source i) (A.target i)
        (A.moduleStage i)
    let _ : _root_.Module R M := _root_.Module.compHom M f
    A.baseChangeSource i (1 ⊗ₜ[A.source i] m) = A.moduleToLimit i m := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
