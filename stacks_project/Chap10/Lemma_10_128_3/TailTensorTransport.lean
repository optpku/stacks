module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap10.Lemma_10_128_3.StageRawKernel
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Limit
public import ReasLib.RingTheory.DirectLimit.Algebra.Tensor
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import ReasLib.RingTheory.DirectLimit.Tail
public import ReasLib.RingTheory.Flatness.IdealTensor
public import ReasLib.RingTheory.Ideal.Tensor.Map

@[expose] public section

universe uR uS uM

open scoped TensorProduct Algebra.TensorProduct.Right

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [_root_.Module S M]

namespace DirectedLocalHomApproximation.Module

/-- Helper for Lemma 10.128.3: the canonical map from a stage module to the limit module sends
`m` to the image of `1 ⊗ m` under the final base-change equivalence. -/
@[stacks 00R6 "stage module limit map"]
noncomputable def stage_module_to_limit_fun
    (A : DirectedLocalHomApproximation.Module f M) (i : A.Λ) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    A.moduleStage i → M :=
  let _ : Algebra (A.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation i).toAlgebra
  fun m ↦ A.finalBaseChange i (1 ⊗ₜ[A.SStage i] m)

/-- Helper for Lemma 10.128.3: the stage-to-limit module map is additive. -/
@[stacks 00R6 "stage module limit map additivity"]
lemma stage_module_to_limit_fun_map_add
    (A : DirectedLocalHomApproximation.Module f M) (i : A.Λ)
    (m n : A.moduleStage i) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    stage_module_to_limit_fun A i (m + n) =
      stage_module_to_limit_fun A i m + stage_module_to_limit_fun A i n := sorry

/-- Helper for Lemma 10.128.3: the stage-to-limit module map is linear over the source-stage ring
when the limit module is viewed through the canonical neutral `sourceToLimit` map. -/
@[stacks 00R6 "stage module limit map scalarity"]
lemma stage_module_to_limit_fun_map_smul
    (A : DirectedLocalHomApproximation.Module f M) (i : A.Λ)
    (r : A.RStage i) (m : A.moduleStage i) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    let _ : _root_.Module R M := _root_.Module.compHom M f
    let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
    let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
    stage_module_to_limit_fun A i (r • m) = r • stage_module_to_limit_fun A i m := sorry

/-- Helper for Lemma 10.128.3: package the stage-to-limit map as a source-stage linear map into
the limit module. -/
@[stacks 00R6 "stage module limit linear map"]
noncomputable def stage_module_to_limit
    (A : DirectedLocalHomApproximation.Module f M) (i : A.Λ) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    let _ : _root_.Module R M := _root_.Module.compHom M f
    let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
    let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
    A.moduleStage i →ₗ[A.RStage i] M :=
  let _ : Algebra (A.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation i).toAlgebra
  let _ : _root_.Module R M := _root_.Module.compHom M f
  let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
  let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
  { toFun := stage_module_to_limit_fun A i
    map_add' := stage_module_to_limit_fun_map_add (A := A) (i := i)
    map_smul' := stage_module_to_limit_fun_map_smul (A := A) (i := i) }

/-- Helper for Lemma 10.128.3: the ambient tensor transport from the raw stage tensor to the
limit-side tensor over `R`, obtained by first sending `M_i` to `M` and then extending the ideal.
-/
@[stacks 00R6 "raw kernel limit tensor map"]
noncomputable def raw_kernel_limit_map
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : _root_.Module R M := _root_.Module.compHom M f
    let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
    let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    I ⊗[A.RStage i] A.moduleStage i →ₗ[A.RStage i]
      Ideal.map (A.toApproximation.sourceToLimit i) I ⊗[R] M :=
  let _ : _root_.Module R M := _root_.Module.compHom M f
  let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
  let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  (Ideal.Map.tensor (S := R) (M := M) I).comp
    ((stage_module_to_limit A i).lTensor I)

/-- Helper for Lemma 10.128.3: after applying the canonical tensor transport to the limit, the
raw stage multiplication agrees with multiplication in the limit module. -/
@[stacks 00R6 "raw kernel limit multiplication comparison"]
lemma raw_kernel_limit_to_module_comp
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : _root_.Module R M := _root_.Module.compHom M f
    let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
    let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : _root_.Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    LinearMap.restrictScalars (A.RStage i)
      (TensorProduct.lift
        ((LinearMap.lsmul R M).comp (Ideal.map (A.toApproximation.sourceToLimit i) I).subtype)) ∘ₗ
      raw_kernel_limit_map A i I =
      stage_module_to_limit A i ∘ₗ
        LinearMap.restrictScalars (A.RStage i) (raw_stage_multiplication A i I) := sorry

/-- Helper for Lemma 10.128.3: every element of the raw stage kernel has zero image under the
canonical limit-side tensor transport. -/
@[stacks 00R6 "raw kernel limit vanishing"]
lemma raw_kernel_limit_zero
    (A : DirectedLocalHomApproximation.Module f M)
    (hflat :
      let _ : _root_.Module R M := _root_.Module.compHom M f
      _root_.Module.Flat R M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I) :
    let _ : _root_.Module R M := _root_.Module.compHom M f
    let _ : Algebra (A.RStage i) R := (A.toApproximation.sourceToLimit i).toAlgebra
    let _ : _root_.Module (A.RStage i) M := _root_.Module.compHom M (f.comp (A.toApproximation.sourceToLimit i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : _root_.Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    raw_kernel_limit_map A i I z.1 = 0 := sorry

/-- Helper for Chap10 Lemma 10 128 3: for the owner whose transition maps are
`tail_target_algHom`, the tail/full comparison sends the base-stage scalar class to the
corresponding scalar in the ambient target limit. -/
@[stacks 00R6 "tail target limit base scalar"]
lemma tail_target_owner_limit_base_scalar
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ) (r : A.RStage i) :
    let _ : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
      fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : DirectedSystem
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      Ring.DirectLimit.algebra
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ tail_target_algHom A i j k h)
    let tailIso :=
      Ring.DirectLimit.Tail.equivTo
        (fun i' j h ↦ A.targetMap i' j h) i A.targetColimit
    tailIso (algebraMap (A.RStage i) tailLimit r) = A.toApproximation.mapToLimit i r := sorry

/-- Helper for Chap10 Lemma 10 128 3: the tail/full comparison for the `tail_target_algHom`
owner is linear over the fixed source stage. -/
@[stacks 00R6 "tail target limit scalarity"]
lemma tail_target_owner_limit_map_smul
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ) (r : A.RStage i) :
    let _ : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
      fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : DirectedSystem
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      Ring.DirectLimit.algebra
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ tail_target_algHom A i j k h)
    let _ : Algebra (A.RStage i) S := (A.toApproximation.mapToLimit i).toAlgebra
    let tailIso :=
      Ring.DirectLimit.Tail.equivTo
        (fun i' j h ↦ A.targetMap i' j h) i A.targetColimit
    ∀ x : tailLimit, tailIso (r • x) = r • tailIso x := sorry

/-- Helper for Lemma 10.128.3: the target-side tail direct limit above `i` is `S`, viewed as an
`R_i`-module through the canonical colimit algebra structure induced by the source-stage maps
into the tail stages. -/
@[stacks 00R6 "tail target limit linear equivalence"]
noncomputable def tail_target_limit_linearEquiv
    (A : DirectedLocalHomApproximation.Module f M) (i : A.Λ) :
    let _ : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
      fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : DirectedSystem
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      Ring.DirectLimit.algebra
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ tail_target_algHom A i j k h)
    let _ : Algebra (A.RStage i) S := (A.toApproximation.mapToLimit i).toAlgebra
    tailLimit ≃ₗ[A.RStage i] S := by
  letI : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
    fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
  letI : DirectedSystem
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
    tail_target_directedSystem A i
  let tailLimit :=
    Ring.DirectLimit
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
  let _ : Algebra (A.RStage i) tailLimit :=
    Ring.DirectLimit.algebra
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ tail_target_algHom A i j k h)
  let _ : Algebra (A.RStage i) S := (A.toApproximation.mapToLimit i).toAlgebra
  let tailIso :=
    Ring.DirectLimit.Tail.equivTo
      (fun i' j h ↦ A.targetMap i' j h) i A.targetColimit
  -- Proof comment: the underlying map is the tail/full ring comparison; source-stage linearity
  -- is exactly the owner scalar-transport lemma proved against the colimit algebra structure.
  exact
    { toFun := tailIso
      invFun := tailIso.symm
      left_inv := by
        intro x
        exact tailIso.left_inv x
      right_inv := by
        intro x
        exact tailIso.right_inv x
      map_add' := by
        intro x y
        exact tailIso.map_add x y
      map_smul' := by
        intro r x
        exact tail_target_owner_limit_map_smul (A := A) (i := i) r x }

/-- Helper for Lemma 10.128.3: the tail/full comparison sends a tail-stage coefficient class to
its ambient image in `S`. -/
@[stacks 00R6 "tail target limit linear equivalence on stages"]
lemma tail_target_limit_linearEquiv_of
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ) (j : Set.Ici i) (r : A.SStage j.1) :
    tail_target_limit_linearEquiv A i
      (Ring.DirectLimit.of
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h) j r) =
      DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1 r := sorry

/-- Helper for Lemma 10.128.3: the tail/full direct-limit comparison sends the base-stage unit
coefficient to the ambient unit. -/
@[stacks 00R6 "tail target limit linear equivalence on one"]
lemma tail_target_limit_linearEquiv_of_base_one
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ) :
    tail_target_limit_linearEquiv A i
      (Ring.DirectLimit.of
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h) ⟨i, le_rfl⟩ (1 : A.SStage i)) =
      (1 : S) := sorry

/-- Helper for Chap10 Lemma 10 128 3: on a pure tensor, transporting the owner tail
`stageTensorMap` through the tail/full comparison identifies it with the ambient target-limit
tensor map. -/
@[stacks 00R6 "tail stage tensor map on pure tensors"]
lemma tailTargetOwnerStageTensorMap_to_targetLimit_tmul
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ)
    {X : Type*} [AddCommGroup X] [_root_.Module (A.RStage i) X]
    (j : Set.Ici i) (r : A.SStage j.1) (x : X) :
    letI : ∀ j' : Set.Ici i, Algebra (A.RStage i) (A.SStage j'.1) :=
      fun j' ↦ (source_stage_to_later_target_hom A i j'.1 j'.2).toAlgebra
    letI : DirectedSystem
        (fun j' : Set.Ici i ↦ A.SStage j'.1)
        (fun j' k' h ↦ (tail_target_algHom A i j' k' h : A.SStage j'.1 →+* A.SStage k'.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j' : Set.Ici i ↦ A.SStage j'.1)
        (fun j' k' h ↦ (tail_target_algHom A i j' k' h : A.SStage j'.1 →+* A.SStage k'.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      Ring.DirectLimit.algebra
        (fun j' : Set.Ici i ↦ A.SStage j'.1)
        (fun j' k' h ↦ tail_target_algHom A i j' k' h)
    let _ : Algebra (A.RStage i) (A.SStage j.1) :=
      (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage j.1) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1).toAlgebra
    let _ : Algebra (A.RStage i) S := (A.toApproximation.mapToLimit i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage j.1) S :=
      Ring.DirectLimit.Algebra.Approximation.Hom.mapToLimit_tower
        A.toApproximation j.2
    let _ : _root_.Module (A.RStage i) (tailLimit ⊗[A.RStage i] X) := inferInstance
    let _ : _root_.Module (A.RStage i) (S ⊗[A.RStage i] X) := inferInstance
    let _ : FunLike
        ((tailLimit ⊗[A.RStage i] X) ≃ₗ[A.RStage i] (S ⊗[A.RStage i] X))
        (tailLimit ⊗[A.RStage i] X) (S ⊗[A.RStage i] X) :=
      EquivLike.toFunLike
    (TensorProduct.congr
      (tail_target_limit_linearEquiv A i)
      (LinearEquiv.refl (A.RStage i) X))
      (Ring.DirectLimit.stageTensorMap
        (A := A.RStage i)
        (R := fun j' : Set.Ici i ↦ A.SStage j'.1)
        (f := fun j' k' h ↦ tail_target_algHom A i j' k' h)
        (X := X) j (r ⊗ₜ[A.RStage i] x)) =
      (LinearMap.rTensor X ((Algebra.linearMap (A.SStage j.1) S).restrictScalars (A.RStage i)))
        (r ⊗ₜ[A.RStage i] x) := sorry

/-- Helper for Chap10 Lemma 10 128 3: transporting the owner tail `stageTensorMap` through the
tail/full comparison identifies it with the ambient target-limit tensor map. -/
@[stacks 00R6 "tail stage tensor map transport"]
lemma tailTargetOwnerStageTensorMap_to_targetLimit
    (A : DirectedLocalHomApproximation.Module f M)
    (i : A.Λ)
    {X : Type*} [AddCommGroup X] [_root_.Module (A.RStage i) X]
    (j : Set.Ici i)
    (z :
      let _ : Algebra (A.RStage i) (A.SStage j.1) :=
        (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
      A.SStage j.1 ⊗[A.RStage i] X) :
    letI : ∀ j' : Set.Ici i, Algebra (A.RStage i) (A.SStage j'.1) :=
      fun j' ↦ (source_stage_to_later_target_hom A i j'.1 j'.2).toAlgebra
    letI : DirectedSystem
        (fun j' : Set.Ici i ↦ A.SStage j'.1)
        (fun j' k' h ↦ (tail_target_algHom A i j' k' h : A.SStage j'.1 →+* A.SStage k'.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j' : Set.Ici i ↦ A.SStage j'.1)
        (fun j' k' h ↦ (tail_target_algHom A i j' k' h : A.SStage j'.1 →+* A.SStage k'.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      Ring.DirectLimit.algebra
        (fun j' : Set.Ici i ↦ A.SStage j'.1)
        (fun j' k' h ↦ tail_target_algHom A i j' k' h)
    let _ : Algebra (A.RStage i) (A.SStage j.1) :=
      (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage j.1) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1).toAlgebra
    let _ : Algebra (A.RStage i) S := (A.toApproximation.mapToLimit i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage j.1) S :=
      Ring.DirectLimit.Algebra.Approximation.Hom.mapToLimit_tower
        A.toApproximation j.2
    let _ : _root_.Module (A.RStage i) (tailLimit ⊗[A.RStage i] X) := inferInstance
    let _ : _root_.Module (A.RStage i) (S ⊗[A.RStage i] X) := inferInstance
    let _ : FunLike
        ((tailLimit ⊗[A.RStage i] X) ≃ₗ[A.RStage i] (S ⊗[A.RStage i] X))
        (tailLimit ⊗[A.RStage i] X) (S ⊗[A.RStage i] X) :=
      EquivLike.toFunLike
    (TensorProduct.congr
      (tail_target_limit_linearEquiv A i)
      (LinearEquiv.refl (A.RStage i) X))
      (Ring.DirectLimit.stageTensorMap
        (A := A.RStage i)
        (R := fun j' : Set.Ici i ↦ A.SStage j'.1)
        (f := fun j' k' h ↦ tail_target_algHom A i j' k' h)
        (X := X) j z) =
      (LinearMap.rTensor X ((Algebra.linearMap (A.SStage j.1) S).restrictScalars (A.RStage i))) z := sorry

end DirectedLocalHomApproximation.Module

end
