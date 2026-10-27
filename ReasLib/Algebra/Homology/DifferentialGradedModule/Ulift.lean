/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded
public import ReasLib.Algebra.Category.DifferentialGraded.Functor
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Universe Lifts of Differential Graded Modules

This file lifts only the carrier modules of a differential graded module while keeping its
coefficient DGA fixed. The construction is the shared universe-management owner for APIs whose
mathematical inputs live in independent carrier universes.
-/

@[expose] public section

noncomputable section

universe u v w l

open CategoryTheory ComplexShape DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable {X Z : ModuleCat.{v} R} {Y : ModuleCat.{w} R}

private theorem ulift_cast {α β : Type v} (h : α = β)
    (h' : ULift.{l} α = ULift.{l} β) (x : α) :
    cast h' (ULift.up x) = ULift.up (cast h x) := by
  cases h
  rfl

private theorem ulift_hom_ext {M N : DifferentialGradedModule.{u, v} A}
    {f g : Hom M N} (h : ∀ n x, f.hom n x = g.hom n x) : f = g := by
  have hh : f.hom = g.hom := funext fun n ↦ LinearMap.ext (h n)
  cases f
  cases g
  cases hh
  rfl

private theorem ulift_castLinearMap {X Y Z : ModuleCat.{v} R} (h : Y = Z)
    (h' : (ModuleCat.uliftFunctor.{l} R).obj Y = (ModuleCat.uliftFunctor.{l} R).obj Z)
    (f : X →ₗ[R] Y) (x : ULift.{l} X) :
    ModuleCat.castLinearMap h'
        (((ModuleCat.uliftFunctor.{l} R).map (ModuleCat.ofHom f)).hom) x =
      ULift.up (ModuleCat.castLinearMap h f x.down) := by
  cases h
  rfl

/-- Lift the module input and output of a curried linear action while keeping its scalar input
unchanged. -/
@[stacks 09JI "universe lift of a graded module action"]
def uliftSmul (f : X →ₗ[R] Y →ₗ[R] Z) :
    ULift.{l} X →ₗ[R] Y →ₗ[R] ULift.{l} Z :=
  (ULift.moduleEquiv (R := R) (M := X)).symm.arrowCongr
    ((LinearEquiv.refl R Y).arrowCongr
      (ULift.moduleEquiv (R := R) (M := Z)).symm) f

/-- A lifted module-input curried map evaluates by lowering its first input and raising the
output. -/
@[simp, stacks 09JI "evaluation of a lifted graded module action"]
theorem uliftSmul_apply (f : X →ₗ[R] Y →ₗ[R] Z) (x : ULift.{l} X) (y : Y) :
    uliftSmul.{u, v, w, l} f x y = ULift.up (f x.down y) := rfl

/-- Lift the second input and output of a curried linear action while keeping its first input
unchanged. -/
@[stacks 09JI "right-input universe lift of a graded module action"]
def uliftRightSmul {X : ModuleCat.{v} R} {Y Z : ModuleCat.{w} R}
    (f : X →ₗ[R] Y →ₗ[R] Z) :
    X →ₗ[R] ULift.{l} Y →ₗ[R] ULift.{l} Z :=
  (LinearEquiv.refl R X).arrowCongr
    ((ULift.moduleEquiv (R := R) (M := Y)).symm.arrowCongr
      (ULift.moduleEquiv (R := R) (M := Z)).symm) f

/-- A right-input lifted curried map evaluates by lowering its second input and raising the output. -/
@[simp, stacks 09JI "evaluation of a right-input lifted graded map"]
theorem uliftRightSmul_apply {X : ModuleCat.{v} R} {Y Z : ModuleCat.{w} R}
    (f : X →ₗ[R] Y →ₗ[R] Z) (x : X) (y : ULift.{l} Y) :
    uliftRightSmul.{u, v, w, l} f x y = ULift.up (f x y.down) := rfl

/-- A right differential graded module with every carrier module lifted to a common larger
universe; the coefficient DGA is unchanged. -/
@[stacks 09JI "universe lift of a differential graded module"]
def ulift (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule.{u, max v l} A where
  X n := (ModuleCat.uliftFunctor.{l} R).obj (M.X n)
  d n := ((ModuleCat.uliftFunctor.{l} R).map (ModuleCat.ofHom (M.d n))).hom
  smul p i := uliftSmul.{u, v, w, l} (M.smul p i)
  d_sq := by
    intro n x
    change ULift.up (M.d (n + 1) (M.d n x.down)) = 0
    rw [M.d_sq]
    rfl
  smul_one := by
    intro r p x
    change ULift.up.{l} (M.smul p 0 x.down (r • A.one)) =
      cast (zeroActionTarget (M := fun n ↦ (ModuleCat.uliftFunctor.{l} R).obj (M.X n)) p)
        (ULift.up (r • x.down))
    erw [ulift_cast (zeroActionTarget (M := M.X) p), M.smul_one]
  smul_mul := by
    intro p i j x a b
    change ULift.up.{l} (M.smul p (i + j) x.down (A.mul i j a b)) =
      cast (mulActionTarget (M := fun n ↦ (ModuleCat.uliftFunctor.{l} R).obj (M.X n)) p i j)
        (ULift.up (M.smul (p + i) j (M.smul p i x.down a) b))
    erw [ulift_cast (mulActionTarget (M := M.X) p i j), M.smul_mul]
  comm_d := by
    intro p i x a
    change ULift.up.{l} (M.d (p + i) (M.smul p i x.down a)) =
      cast (dLeftActionTarget (M := fun n ↦ (ModuleCat.uliftFunctor.{l} R).obj (M.X n)) p i)
        (ULift.up (M.smul (p + 1) i (M.d p x.down) a)) +
        (p.negOnePow : R) •
          cast (dRightActionTarget (M := fun n ↦ (ModuleCat.uliftFunctor.{l} R).obj (M.X n)) p i)
            (ULift.up (M.smul p (i + 1) x.down (A.d i a)))
    erw [ulift_cast (dLeftActionTarget (M := M.X) p i),
      ulift_cast (dRightActionTarget (M := M.X) p i), M.comm_d]
    rfl

/-- A homogeneous map of differential graded modules induces a homogeneous map between their
universe lifts. -/
@[stacks 09JI "homogeneous map between universe-lifted differential graded modules"]
def uliftGradedHom {M N : DifferentialGradedModule.{u, v} A} {k : ℤ}
    (f : GradedHom A M N k) :
    GradedHom A (ulift.{u, v, w, l} M) (ulift.{u, v, w, l} N) k :=
  ⟨fun n ↦ ((ModuleCat.uliftFunctor.{l} R).map (ModuleCat.ofHom (f n))).hom, by
    intro n m x a
    change ULift.up.{l} (f (n + m) (M.smul n m x.down a)) =
      cast (congrArg (fun t : ℤ ↦ ULift.{l} (N.X t)) (gradedHom_smul_index n m k))
        (ULift.up (N.smul (n + k) m (f n x.down) a))
    erw [ulift_cast (congrArg (fun t : ℤ ↦ (N.X t : Type v))
      (gradedHom_smul_index n m k))]
    exact congrArg ULift.up (f.property n m x.down a)⟩

/-- Lower a homogeneous map between universe-lifted differential graded modules. -/
@[stacks 09JI "lower a homogeneous map between lifted differential graded modules"]
def downGradedHom {M N : DifferentialGradedModule.{u, v} A} {k : ℤ}
    (f : GradedHom A (ulift.{u, v, w, l} M) (ulift.{u, v, w, l} N) k) :
    GradedHom A M N k :=
  ⟨fun n ↦
    { toFun := fun x ↦ (f n (ULift.up x)).down
      map_add' := by
        intro x y
        exact congrArg ULift.down (map_add (f n) (ULift.up x) (ULift.up y))
      map_smul' := by
        intro r x
        exact congrArg ULift.down (map_smul (f n) r (ULift.up x)) }, by
    intro n m x a
    have h := congrArg ULift.down (f.property n m (ULift.up x) a)
    change (f (n + m) (ULift.up (M.smul n m x a))).down =
      (cast (congrArg (fun t : ℤ ↦ ULift.{l} (N.X t)) (gradedHom_smul_index n m k))
        (ULift.up (N.smul (n + k) m (f n (ULift.up x)).down a))).down at h
    erw [ulift_cast (congrArg (fun t : ℤ ↦ (N.X t : Type v))
      (gradedHom_smul_index n m k))] at h
    exact h⟩

/-- Lowering a homogeneous map evaluates by raising, applying, and lowering. -/
@[simp, stacks 09JI "evaluation of a lowered homogeneous differential graded module map"]
theorem downGradedHom_apply {M N : DifferentialGradedModule.{u, v} A} {k : ℤ}
    (f : GradedHom A (ulift.{u, v, w, l} M) (ulift.{u, v, w, l} N) k)
    (n : ℤ) (x : M.X n) :
    downGradedHom.{u, v, w, l} f n x = (f n (ULift.up x)).down := rfl

/-- Lowering a lifted homogeneous differential graded module map recovers the original map. -/
@[simp, stacks 09JI "lower after lift for homogeneous differential graded module maps"]
theorem downGradedHom_uliftGradedHom
    {M N : DifferentialGradedModule.{u, v} A} {k : ℤ} (f : GradedHom A M N k) :
    downGradedHom.{u, v, w, l} (uliftGradedHom.{u, v, w, l} f) = f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  rfl

/-- Lifting a lowered homogeneous map between lifted DG modules recovers that map. -/
@[simp, stacks 09JI "lift after lower for homogeneous differential graded module maps"]
theorem uliftGradedHom_downGradedHom
    {M N : DifferentialGradedModule.{u, v} A} {k : ℤ}
    (f : GradedHom A (ulift.{u, v, w, l} M) (ulift.{u, v, w, l} N) k) :
    uliftGradedHom.{u, v, w, l} (downGradedHom.{u, v, w, l} f) = f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  rfl

/-- Universe lifting gives a linear equivalence on every graded hom module. -/
@[stacks 09JI "linear equivalence on graded homs under universe lift"]
def gradedHomLinearEquiv (M N : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    GradedHom A M N k ≃ₗ[R]
      GradedHom A (ulift.{u, v, w, l} M) (ulift.{u, v, w, l} N) k where
  toFun := uliftGradedHom
  invFun := downGradedHom
  left_inv := downGradedHom_uliftGradedHom
  right_inv := uliftGradedHom_downGradedHom
  map_add' := by
    intro f g
    apply Subtype.ext
    funext n
    apply LinearMap.ext
    intro x
    rfl
  map_smul' := by
    intro r f
    apply Subtype.ext
    funext n
    apply LinearMap.ext
    intro x
    rfl

/-- The forward map of `gradedHomLinearEquiv` lifts a homogeneous map. -/
@[simp, stacks 09JI "forward map of the lifted graded-hom linear equivalence"]
theorem gradedHomLinearEquiv_apply (M N : DifferentialGradedModule.{u, v} A)
    (k : ℤ) (f : GradedHom A M N k) :
    gradedHomLinearEquiv.{u, v, w, l} M N k f = uliftGradedHom.{u, v, w, l} f := rfl

/-- The inverse map of `gradedHomLinearEquiv` lowers a homogeneous map. -/
@[simp, stacks 09JI "inverse map of the lifted graded-hom linear equivalence"]
theorem gradedHomLinearEquiv_symm_apply (M N : DifferentialGradedModule.{u, v} A)
    (k : ℤ)
    (f : GradedHom A (ulift.{u, v, w, l} M) (ulift.{u, v, w, l} N) k) :
    (gradedHomLinearEquiv.{u, v, w, l} M N k).symm f =
      downGradedHom.{u, v, w, l} f := rfl

/-- A morphism of differential graded modules induces a morphism between their universe lifts. -/
@[stacks 09JI "morphism between universe-lifted differential graded modules"]
def uliftHom {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    ulift.{u, v, w, l} M ⟶ ulift.{u, v, w, l} N where
  hom n := ((ModuleCat.uliftFunctor.{l} R).map (ModuleCat.ofHom (f.hom n))).hom
  comm_d := by
    intro n x
    exact congrArg ULift.up (f.comm_d n x.down)
  comm_smul := by
    intro p i x a
    exact congrArg ULift.up (f.comm_smul p i x.down a)

/-- Lower a morphism between universe-lifted differential graded modules. -/
@[stacks 09JI "lower a morphism between lifted differential graded modules"]
def downHom {M N : DifferentialGradedModule.{u, v} A}
    (f : ulift.{u, v, w, l} M ⟶ ulift.{u, v, w, l} N) : M ⟶ N where
  hom n :=
    { toFun := fun x ↦ (f.hom n (ULift.up x)).down
      map_add' := by
        intro x y
        exact congrArg ULift.down (map_add (f.hom n) (ULift.up x) (ULift.up y))
      map_smul' := by
        intro r x
        exact congrArg ULift.down (map_smul (f.hom n) r (ULift.up x)) }
  comm_d := by
    intro n x
    exact congrArg ULift.down (f.comm_d n (ULift.up x))
  comm_smul := by
    intro p i x a
    exact congrArg ULift.down (f.comm_smul p i (ULift.up x) a)

/-- Lowering a morphism between lifted DG modules evaluates by raising, applying, and lowering. -/
@[simp, stacks 09JI "evaluation of a lowered differential graded module morphism"]
theorem downHom_apply {M N : DifferentialGradedModule.{u, v} A}
    (f : ulift.{u, v, w, l} M ⟶ ulift.{u, v, w, l} N)
    (n : ℤ) (x : M.X n) :
    (downHom.{u, v, w, l} f).hom n x = (f.hom n (ULift.up x)).down := rfl

/-- Lowering a lifted differential graded module morphism recovers the original morphism. -/
@[simp, stacks 09JI "lower after lift for differential graded module morphisms"]
theorem downHom_uliftHom {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    downHom.{u, v, w, l} (uliftHom.{u, v, w, l} f) = f := by
  apply ulift_hom_ext
  intro n x
  rfl

/-- Lifting a lowered morphism between lifted DG modules recovers that morphism. -/
@[simp, stacks 09JI "lift after lower for differential graded module morphisms"]
theorem uliftHom_downHom {M N : DifferentialGradedModule.{u, v} A}
    (f : ulift.{u, v, w, l} M ⟶ ulift.{u, v, w, l} N) :
    uliftHom.{u, v, w, l} (downHom.{u, v, w, l} f) = f := by
  apply ulift_hom_ext
  intro n x
  rfl

/-- Universe lifting is functorial on differential graded modules over a fixed DGA. -/
@[stacks 09JI "universe-lift functor on differential graded modules"]
def uliftFunctor (A : CochainDGAlgebra.{u, w} R) :
    DifferentialGradedModule.{u, v} A ⥤
      DifferentialGradedModule.{u, max v l} A where
  obj := ulift
  map := uliftHom
  map_id := by
    intro M
    apply ulift_hom_ext
    intro n x
    rfl
  map_comp := by
    intro M N P f g
    apply ulift_hom_ext
    intro n x
    rfl

/-- The differential graded module universe-lift functor uses `ulift` on objects. -/
@[simp, stacks 09JI "differential graded module universe-lift functor on objects"]
theorem uliftFunctor_obj (A : CochainDGAlgebra.{u, w} R)
    (M : DifferentialGradedModule.{u, v} A) :
    (uliftFunctor.{u, v, w, l} A).obj M = ulift.{u, v, w, l} M := rfl

/-- The differential graded module universe-lift functor uses `uliftHom` on morphisms. -/
@[simp, stacks 09JI "differential graded module universe-lift functor on morphisms"]
theorem uliftFunctor_map (A : CochainDGAlgebra.{u, w} R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    (uliftFunctor.{u, v, w, l} A).map f = uliftHom.{u, v, w, l} f := rfl

/-- Universe lifting is additive on differential graded module morphisms. -/
@[stacks 09JI "additive universe-lift functor on differential graded modules"]
instance uliftFunctorAdditive (A : CochainDGAlgebra.{u, w} R) :
    (uliftFunctor.{u, v, w, l} A).Additive where
  map_add := by
    intro M N f g
    apply ulift_hom_ext
    intro n x
    rfl

/-- Universe lifting is `R`-linear on differential graded module morphisms. -/
@[stacks 09JI "linear universe-lift functor on differential graded modules"]
instance uliftFunctorLinear (A : CochainDGAlgebra.{u, w} R) :
    Functor.Linear R (uliftFunctor.{u, v, w, l} A) where
  map_smul := by
    intro M N r f
    apply ulift_hom_ext
    intro n x
    rfl

/-- The differential graded module universe-lift functor is fully faithful on morphisms. -/
@[stacks 09JI "full faithfulness of the differential graded module universe lift"]
def fullyFaithfulUliftFunctor (A : CochainDGAlgebra.{u, w} R) :
    (uliftFunctor.{u, v, w, l} A).FullyFaithful where
  preimage f := downHom f
  map_preimage := by
    intro M N f
    exact uliftHom_downHom f
  preimage_map := by
    intro M N f
    exact downHom_uliftHom f

/-- The differential graded module universe-lift functor is full. -/
@[stacks 09JI "full instance for the differential graded module universe lift"]
instance uliftFunctorFull (A : CochainDGAlgebra.{u, w} R) :
    (uliftFunctor.{u, v, w, l} A).Full := (fullyFaithfulUliftFunctor A).full

/-- The differential graded module universe-lift functor is faithful. -/
@[stacks 09JI "faithful instance for the differential graded module universe lift"]
instance uliftFunctorFaithful (A : CochainDGAlgebra.{u, w} R) :
    (uliftFunctor.{u, v, w, l} A).Faithful := (fullyFaithfulUliftFunctor A).faithful

/-- Universe lifting is a differential graded functor on modules over a fixed DGA. -/
@[stacks 09JI "DG universe-lift functor on differential graded modules"]
def uliftDgFunctor (A : CochainDGAlgebra.{u, w} R) :
    DgFunctor R (DifferentialGradedModule.{u, v} A)
      (DifferentialGradedModule.{u, max v l} A) where
  obj := ulift
  map := uliftGradedHom
  map_add := by
    intro M N k f g
    exact (gradedHomLinearEquiv M N k).map_add f g
  map_smul := by
    intro M N k r f
    exact (gradedHomLinearEquiv M N k).map_smul r f
  map_d := by
    intro M N k f
    apply Subtype.ext
    funext n
    apply LinearMap.ext
    intro x
    change ULift.up
        (ModuleCat.castLinearMap (congrArg N.X (gradedHom_differential_left_index n k))
            ((N.d (n + k)).comp (f n)) x.down -
          (k.negOnePow : R) •
            ModuleCat.castLinearMap (congrArg N.X (gradedHom_differential_right_index n k))
              ((f (n + 1)).comp (M.d n)) x.down) =
      ModuleCat.castLinearMap
          (congrArg (ulift N).X (gradedHom_differential_left_index n k))
          (((ulift N).d (n + k)).comp (uliftGradedHom f n)) x -
        (k.negOnePow : R) •
          ModuleCat.castLinearMap
            (congrArg (ulift N).X (gradedHom_differential_right_index n k))
            ((uliftGradedHom f (n + 1)).comp ((ulift M).d n)) x
    exact (congrArg₂ (fun y z : ULift.{l} (N.X (n + (k + 1))) ↦
        y - (k.negOnePow : R) • z)
      (ulift_castLinearMap (congrArg N.X (gradedHom_differential_left_index n k))
        (congrArg (ulift N).X (gradedHom_differential_left_index n k))
        ((N.d (n + k)).comp (f n)) x)
      (ulift_castLinearMap (congrArg N.X (gradedHom_differential_right_index n k))
        (congrArg (ulift N).X (gradedHom_differential_right_index n k))
        ((f (n + 1)).comp (M.d n)) x)).symm
  map_id := by
    intro M
    apply Subtype.ext
    funext n
    apply LinearMap.ext
    intro x
    change ULift.up (ModuleCat.castLinearMap (congrArg M.X (add_zero n).symm)
        LinearMap.id x.down) =
      ModuleCat.castLinearMap (congrArg (ulift M).X (add_zero n).symm) LinearMap.id x
    exact (ulift_castLinearMap (congrArg M.X (add_zero n).symm) _ LinearMap.id x).symm
  map_comp := by
    intro M N P i j g f
    apply Subtype.ext
    funext n
    apply LinearMap.ext
    intro x
    change ULift.up (ModuleCat.castLinearMap (congrArg P.X (gradedHom_comp_index n i j))
        ((g (n + i)).comp (f n)) x.down) =
      ModuleCat.castLinearMap (congrArg (ulift P).X (gradedHom_comp_index n i j))
        ((uliftGradedHom g (n + i)).comp (uliftGradedHom f n)) x
    exact (ulift_castLinearMap (congrArg P.X (gradedHom_comp_index n i j)) _
      ((g (n + i)).comp (f n)) x).symm

/-- Degreewise carrier of a universe-lifted differential graded module. -/
@[simp, stacks 09JI "degreewise carrier of a lifted differential graded module"]
theorem ulift_X (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (ulift.{u, v, w, l} M).X n = (ModuleCat.uliftFunctor.{l} R).obj (M.X n) := rfl

/-- Degreewise differential of a universe-lifted differential graded module. -/
@[simp, stacks 09JI "differential of a lifted differential graded module"]
theorem ulift_d (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (ulift.{u, v, w, l} M).d n =
      ((ModuleCat.uliftFunctor.{l} R).map (ModuleCat.ofHom (M.d n))).hom := rfl

/-- The lifted differential lowers, applies the original differential, and raises again. -/
@[simp, stacks 09JI "evaluation of a lifted differential"]
theorem ulift_d_apply (M : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (ulift.{u, v, w, l} M).X n) :
    (ulift.{u, v, w, l} M).d n x = ULift.up (M.d n x.down) := rfl

/-- The lifted right action lowers, applies the original action, and raises again. -/
@[simp, stacks 09JI "evaluation of a lifted differential graded module action"]
theorem ulift_smul (M : DifferentialGradedModule.{u, v} A) (p i : ℤ)
    (x : (ulift.{u, v, w, l} M).X p) (a : A.X i) :
    (ulift.{u, v, w, l} M).smul p i x a = ULift.up (M.smul p i x.down a) := rfl

/-- A lifted homogeneous map lowers, applies the original map, and raises again. -/
@[simp, stacks 09JI "evaluation of a lifted homogeneous module map"]
theorem uliftGradedHom_apply {M N : DifferentialGradedModule.{u, v} A} {k : ℤ}
    (f : GradedHom A M N k) (n : ℤ) (x : (ulift.{u, v, w, l} M).X n) :
    uliftGradedHom.{u, v, w, l} f n x = ULift.up (f n x.down) := rfl

/-- A lifted module morphism lowers, applies the original morphism, and raises again. -/
@[simp, stacks 09JI "evaluation of a lifted differential graded module morphism"]
theorem uliftHom_apply {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N)
    (n : ℤ) (x : (ulift.{u, v, w, l} M).X n) :
    (uliftHom.{u, v, w, l} f).hom n x = ULift.up (f.hom n x.down) := rfl

/-- The DG universe-lift functor uses `ulift` on objects. -/
@[simp, stacks 09JI "DG universe-lift functor on objects"]
theorem uliftDgFunctor_obj (A : CochainDGAlgebra.{u, w} R)
    (M : DifferentialGradedModule.{u, v} A) :
    (uliftDgFunctor.{u, v, w, l} A).obj M = ulift.{u, v, w, l} M := rfl

/-- The DG universe-lift functor uses `uliftGradedHom` on homogeneous maps. -/
@[simp, stacks 09JI "DG universe-lift functor on homogeneous maps"]
theorem uliftDgFunctor_map (A : CochainDGAlgebra.{u, w} R)
    {M N : DifferentialGradedModule.{u, v} A} {k : ℤ} (f : GradedHom A M N k) :
    (uliftDgFunctor.{u, v, w, l} A).map f = uliftGradedHom.{u, v, w, l} f := rfl

/-- Universe lift of a cochain complex of modules. -/
@[stacks 09JI "universe lift of a cochain complex"]
abbrev uliftComplex (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{max v l} R) ℤ :=
  ((ModuleCat.uliftFunctor.{l} R).mapHomologicalComplex (up ℤ)).obj K

/-- Degreewise carrier of a universe-lifted cochain complex. -/
@[simp, stacks 09JI "degreewise carrier of a lifted cochain complex"]
theorem uliftComplex_X (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    (uliftComplex.{u, v, l} K).X n =
      (ModuleCat.uliftFunctor.{l} R).obj (K.X n) := rfl

/-- Differential of a universe-lifted cochain complex. -/
@[simp, stacks 09JI "differential of a lifted cochain complex"]
theorem uliftComplex_d (K : CochainComplex (ModuleCat.{v} R) ℤ) (i j : ℤ) :
    (uliftComplex.{u, v, l} K).d i j =
      (ModuleCat.uliftFunctor.{l} R).map (K.d i j) := rfl

/-- The underlying complex of a lifted differential graded module is its universe-lifted
underlying complex. -/
@[simp, stacks 09JI "underlying complex of a lifted differential graded module"]
theorem ulift_toCochainComplex (M : DifferentialGradedModule.{u, v} A) :
    (ulift.{u, v, w, l} M).toCochainComplex =
      uliftComplex.{u, v, l} M.toCochainComplex := by
  refine HomologicalComplex.ext (C₁ := (ulift.{u, v, w, l} M).toCochainComplex)
    (C₂ := uliftComplex.{u, v, l} M.toCochainComplex) rfl ?_
  intro i j h
  have hij : i + 1 = j := h
  subst j
  change CochainComplex.of.d _ (fun n ↦ ModuleCat.ofHom ((ulift M).d n)) i (i + 1) ≫ 𝟙 _ =
    𝟙 _ ≫ (ModuleCat.uliftFunctor R).map (CochainComplex.of.d _ _ i (i + 1))
  rw [Category.comp_id, Category.id_comp, CochainComplex.of_d, CochainComplex.of_d]
  rfl

end DifferentialGradedModule
