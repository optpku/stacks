/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Duals of Differential Graded Bimodules

For a differential graded `(A, B)`-bimodule `T`, this file constructs the concrete
`(B, A)`-bimodule `Hom_B(T, B)`.  Its right `A`-action is the internal-Hom action by
precomposition, and its left `B`-action is postcomposition with left multiplication on the
regular `B`-module.

The second half constructs the canonical evaluation comparison
`N tensor_B Hom_B(T, B) ⟶ Hom_B(T, N)` before passing to derived categories.  The map is
defined through the existing tensor-Hom adjunction, so the balancing quotient is not duplicated.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

namespace Dual

private theorem castLinearMap_apply {M N N' : ModuleCat.{v} R} (h : N = N')
    (f : M →ₗ[R] N) (x : M) :
    ModuleCat.castLinearMap h f x =
      cast (congrArg (fun X : ModuleCat.{v} R ↦ (X : Type v)) h) (f x) := by
  cases h
  rfl

private theorem castLinearMap_add {M N N' : ModuleCat.{v} R} (h : N = N')
    (f g : M →ₗ[R] N) :
    ModuleCat.castLinearMap h (f + g) =
      ModuleCat.castLinearMap h f + ModuleCat.castLinearMap h g := by
  cases h
  rfl

private theorem castLinearMap_smul {M N N' : ModuleCat.{v} R} (h : N = N')
    (r : R) (f : M →ₗ[R] N) :
    ModuleCat.castLinearMap h (r • f) = r • ModuleCat.castLinearMap h f := by
  cases h
  rfl

private theorem cast_add (X : ℤ → ModuleCat.{v} R) {i j : ℤ} (h : i = j)
    (x y : X i) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) x +
        cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) y := by
  cases h
  rfl

private theorem cast_smul (X : ℤ → ModuleCat.{v} R) {i j : ℤ} (h : i = j)
    (r : R) (x : X i) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) x := by
  cases h
  rfl

private theorem cast_mul_left (B : CochainDGAlgebra.{u, v} R) {i i' : ℤ}
    (h : i = i') (j : ℤ) (b : B.X i) (c : B.X j) :
    B.mul i' j (cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) h) b) c =
      cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) (congrArg (· + j) h))
        (B.mul i j b c) := by
  cases h
  rfl

private theorem cast_smul_left (N : DifferentialGradedModule.{u, v} B) {p p' : ℤ}
    (h : p = p') (i : ℤ) (n : N.X p) (b : B.X i) :
    N.smul p' i (cast (congrArg (fun k : ℤ ↦ (N.X k : Type v)) h) n) b =
      cast (congrArg (fun k : ℤ ↦ (N.X k : Type v)) (congrArg (· + i) h))
        (N.smul p i n b) := by
  cases h
  rfl

private theorem cast_smul_right (N : DifferentialGradedModule.{u, v} B) (p : ℤ) {i i' : ℤ}
    (h : i = i') (n : N.X p) (b : B.X i) :
    N.smul p i' n (cast (congrArg (fun k : ℤ ↦ (B.X k : Type v)) h) b) =
      cast (congrArg (fun k : ℤ ↦ (N.X k : Type v)) (congrArg (p + ·) h))
        (N.smul p i n b) := by
  cases h
  rfl

private theorem cast_mul_right (B : CochainDGAlgebra.{u, v} R) (i : ℤ) {j j' : ℤ}
    (h : j = j') (b : B.X i) (c : B.X j) :
    B.mul i j' b (cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) h) c) =
      cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) (congrArg (i + ·) h))
        (B.mul i j b c) := by
  cases h
  rfl

private theorem castGradedHom_apply {C : CochainDGAlgebra.{u, v} R}
    {L M : DifferentialGradedModule.{u, v} C} {i j : ℤ} (h : i = j)
    (f : DifferentialGradedModule.GradedHom C L M i) (n : ℤ) (x : L.X n) :
    (cast (congrArg (fun k : ℤ ↦ DifferentialGradedModule.GradedHom C L M k) h) f) n x =
      cast (congrArg (fun k : ℤ ↦ (M.X (n + k) : Type v)) h) (f n x) := by
  cases h
  rfl

/-- Left multiplication by a homogeneous element of `B`, as a homogeneous endomorphism of the
regular right `B`-module. -/
def leftMultiplication (B : CochainDGAlgebra.{u, v} R) (i : ℤ) (b : B.X i) :
    DifferentialGradedModule.GradedHom B B.regularModule B.regularModule i :=
  ⟨fun p ↦ ModuleCat.castLinearMap (congrArg B.X (add_comm i p)) (B.mul i p b), by
    intro n m x a
    change ModuleCat.castLinearMap _ (B.mul i (n + m) b) (B.mul n m x a) =
      cast _ (B.mul (n + i) m
        (ModuleCat.castLinearMap _ (B.mul i n b) x) a)
    simp only [castLinearMap_apply]
    rw [cast_mul_left B (add_comm i n) m]
    rw [← B.mul_assoc i n m b x a]
    simp only [cast_cast]⟩

/-- Homogeneous left multiplication on the regular module evaluates as multiplication in `B`.
-/
theorem leftMultiplication_apply (B : CochainDGAlgebra.{u, v} R) (i p : ℤ)
    (b : B.X i) (x : B.X p) :
    leftMultiplication B i b p x =
      cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) (add_comm i p))
        (B.mul i p b x) := by
  exact ModuleCat.castLinearMap_apply (congrArg B.X (add_comm i p)) (B.mul i p b) x

/-- Postcomposition by left multiplication, with the output degree reordered for a left
`B`-action on `Hom_B(T, B)`. -/
def leftMulValue (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (i p : ℤ) (b : B.X i) (f : (internalHom T B.regularModule).X p) :
    (internalHom T B.regularModule).X (i + p) :=
  cast
    (congrArg (fun n : ℤ ↦ ((internalHom T B.regularModule).X n : Type v))
      (add_comm p i))
    (internalHomMap T (leftMultiplication B i b) p f)

private theorem leftMulValue_apply (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (i p s : ℤ) (b : B.X i) (f : (internalHom T B.regularModule).X p) (t : T.X s) :
    asGradedHom T B.regularModule (leftMulValue T i p b f) s t =
      cast (congrArg (fun k : ℤ ↦ (B.X k : Type v)) (add_left_comm i s p))
        (B.mul i (s + p) b ((asGradedHom T B.regularModule f) s t)) := by
  change (cast (congrArg
    (fun k : ℤ ↦ DifferentialGradedModule.GradedHom B T.toRightModule B.regularModule k)
    (add_comm p i)) (DifferentialGradedModule.gradedHomComp (leftMultiplication B i b) f)) s t = _
  rw [castGradedHom_apply (add_comm p i)]
  change cast (congrArg (fun k : ℤ ↦ (B.X (s + k) : Type v)) (add_comm p i))
    (ModuleCat.castLinearMap
      (congrArg B.X (DifferentialGradedModule.gradedHom_comp_index s p i))
      ((leftMultiplication B i b (s + p)).comp (asGradedHom T B.regularModule f s)) t) = _
  simp only [castLinearMap_apply]
  erw [LinearMap.comp_apply, leftMultiplication_apply]
  simp only [cast_cast] <;> rfl

/-- Postcomposition by left multiplication is bilinear in the algebra element and the
internal-Hom element. -/
def leftMul (T : DifferentialGradedBimodule.{u, v, v, v} A B) (i p : ℤ) :
    B.X i →ₗ[R] (internalHom T B.regularModule).X p →ₗ[R]
      (internalHom T B.regularModule).X (i + p) where
  toFun := fun b ↦
    { toFun := leftMulValue T i p b
      map_add' := by
        intro f g
        exact (congrArg
          (cast (congrArg (fun n : ℤ ↦ ((internalHom T B.regularModule).X n : Type v))
            (add_comm p i))) ((internalHomMap T (leftMultiplication B i b) p).map_add f g)).trans
          (cast_add (internalHom T B.regularModule).X (add_comm p i) _ _)
      map_smul' := by
        intro r f
        exact (congrArg
          (cast (congrArg (fun n : ℤ ↦ ((internalHom T B.regularModule).X n : Type v))
            (add_comm p i))) ((internalHomMap T (leftMultiplication B i b) p).map_smul r f)).trans
          (cast_smul (internalHom T B.regularModule).X (add_comm p i) r _) }
  map_add' := by
    intro b c
    apply LinearMap.ext
    intro f
    change leftMulValue T i p (b + c) f = leftMulValue T i p b f + leftMulValue T i p c f
    unfold leftMulValue
    rw [← cast_add (internalHom T B.regularModule).X (add_comm p i)]
    apply congrArg (cast
      (congrArg (fun n : ℤ ↦ ((internalHom T B.regularModule).X n : Type v))
        (add_comm p i)))
    apply Subtype.ext
    funext s
    apply LinearMap.ext
    intro x
    change ModuleCat.castLinearMap
        (congrArg B.X (DifferentialGradedModule.gradedHom_comp_index s p i))
        ((leftMultiplication B i (b + c) (s + p)).comp (asGradedHom T B.regularModule f s)) x =
      ModuleCat.castLinearMap
          (congrArg B.X (DifferentialGradedModule.gradedHom_comp_index s p i))
          ((leftMultiplication B i b (s + p)).comp (asGradedHom T B.regularModule f s)) x +
        ModuleCat.castLinearMap
          (congrArg B.X (DifferentialGradedModule.gradedHom_comp_index s p i))
          ((leftMultiplication B i c (s + p)).comp (asGradedHom T B.regularModule f s)) x
    simp only [castLinearMap_apply]
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      leftMultiplication_apply, leftMultiplication_apply, leftMultiplication_apply]
    simp only [map_add, LinearMap.add_apply]
    erw [cast_add B.X (add_comm i (s + p)),
      cast_add B.X (DifferentialGradedModule.gradedHom_comp_index s p i)]
  map_smul' := by
    intro r b
    apply LinearMap.ext
    intro f
    change leftMulValue T i p (r • b) f = r • leftMulValue T i p b f
    unfold leftMulValue
    rw [← cast_smul (internalHom T B.regularModule).X (add_comm p i)]
    apply congrArg (cast
      (congrArg (fun n : ℤ ↦ ((internalHom T B.regularModule).X n : Type v))
        (add_comm p i)))
    apply Subtype.ext
    funext s
    apply LinearMap.ext
    intro x
    change ModuleCat.castLinearMap
        (congrArg B.X (DifferentialGradedModule.gradedHom_comp_index s p i))
        ((leftMultiplication B i (r • b) (s + p)).comp (asGradedHom T B.regularModule f s)) x =
      r • ModuleCat.castLinearMap
        (congrArg B.X (DifferentialGradedModule.gradedHom_comp_index s p i))
        ((leftMultiplication B i b (s + p)).comp (asGradedHom T B.regularModule f s)) x
    simp only [castLinearMap_apply]
    erw [LinearMap.comp_apply, LinearMap.comp_apply,
      leftMultiplication_apply, leftMultiplication_apply]
    simp only [map_smul, LinearMap.smul_apply]
    erw [cast_smul B.X (add_comm i (s + p)),
      cast_smul B.X (DifferentialGradedModule.gradedHom_comp_index s p i)]

private theorem leftMul_comm_right (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (i p j : ℤ) (b : B.X i) (f : (internalHom T B.regularModule).X p) (a : A.X j) :
    cast (congrArg (fun k : ℤ ↦ ((internalHom T B.regularModule).X k : Type v))
      (add_assoc i p j))
      ((internalHom T B.regularModule).smul (i + p) j (leftMul T i p b f) a) =
      leftMul T i (p + j) b ((internalHom T B.regularModule).smul p j f a) := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro t
  change (cast (congrArg
    (fun k : ℤ ↦ DifferentialGradedModule.GradedHom B T.toRightModule B.regularModule k)
    (add_assoc i p j))
    ((internalHom T B.regularModule).smul (i + p) j (leftMulValue T i p b f) a)) s t =
      asGradedHom T B.regularModule
        (leftMulValue T i (p + j) b ((internalHom T B.regularModule).smul p j f a)) s t
  rw [castGradedHom_apply (add_assoc i p j)]
  erw [internalHom_smul_apply T B.regularModule (i + p) j s
    (leftMulValue T i p b f) a t]
  erw [leftMulValue_apply T i p (j + s) b f (T.leftMul j s a t)]
  erw [leftMulValue_apply T i (p + j) s b
    ((internalHom T B.regularModule).smul p j f a) t]
  erw [internalHom_smul_apply T B.regularModule p j s f a t]
  erw [cast_mul_right B i (internalHomActionDegree j s p)]
  dsimp only [CochainDGAlgebra.regularModule, asGradedHom] at *
  simp only [cast_cast]

/-- The compatible left `B`-action on `Hom_B(T, B)` obtained by homogeneous
postcomposition. -/
def leftAction (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    LeftAction B (internalHom T B.regularModule) where
  leftMul := leftMul T
  left_assoc := by
    intro i j p b c f
    apply Subtype.ext
    funext s
    apply LinearMap.ext
    intro t
    change asGradedHom T B.regularModule
        (leftMulValue T (i + j) p (B.mul i j b c) f) s t =
      (cast (congrArg
        (fun k : ℤ ↦ DifferentialGradedModule.GradedHom B T.toRightModule B.regularModule k)
        (add_assoc i j p).symm)
        (leftMulValue T i (j + p) b (leftMulValue T j p c f))) s t
    rw [castGradedHom_apply (add_assoc i j p).symm,
      leftMulValue_apply, leftMulValue_apply, leftMulValue_apply]
    rw [cast_mul_right B i (add_left_comm j s p), ← B.mul_assoc i j (s + p) b c ((asGradedHom T B.regularModule f) s t)]
    dsimp only [CochainDGAlgebra.regularModule, asGradedHom] at *
    simp only [cast_cast]
  one_left := by
    intro p f
    apply Subtype.ext
    funext s
    apply LinearMap.ext
    intro t
    change asGradedHom T B.regularModule (leftMulValue T 0 p B.one f) s t =
      (cast (congrArg
        (fun k : ℤ ↦ DifferentialGradedModule.GradedHom B T.toRightModule B.regularModule k)
        (zero_add p).symm) f) s t
    rw [castGradedHom_apply (zero_add p).symm, leftMulValue_apply]
    have h := congrArg
      (cast (congrArg (fun k : ℤ ↦ (B.X k : Type v))
        (congrArg (s + ·) (zero_add p).symm)))
      (B.one_mul (s + p) ((asGradedHom T B.regularModule f) s t))
    simpa only [cast_cast, asGradedHom, CochainDGAlgebra.regularModule] using h
  comm_right := by
    exact leftMul_comm_right T
  d_leftMul := sorry

/-- The left action on the dual internal Hom is homogeneous postcomposition by left
multiplication on `B`. -/
theorem asGradedHom_leftMulValue (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (i p : ℤ) (b : B.X i) (f : (internalHom T B.regularModule).X p) :
    asGradedHom T B.regularModule (leftMulValue T i p b f) =
      cast
        (congrArg
          (fun k : ℤ ↦ DifferentialGradedModule.GradedHom
            B T.toRightModule B.regularModule k)
          (add_comm p i))
        (DifferentialGradedModule.gradedHomComp (leftMultiplication B i b)
          (asGradedHom T B.regularModule f)) := by
  rfl

end Dual

/-- Lemma 22.33.9 (1) (0BZ0): the dual of a differential graded `(A, B)`-bimodule
`T` is the concrete `(B, A)`-bimodule `Hom_B(T, B)`. -/
@[stacks 0BZ0 "dual differential graded bimodule"]
def dual (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    DifferentialGradedBimodule.{u, v, v, v} B A :=
  (Dual.leftAction T).toBimodule

namespace Dual

/-- The right `A`-module underlying `T.dual` is the fixed-source internal Hom
`Hom_B(T, B)`. -/
@[simp, stacks 0BZ0 "underlying right-module specification of the dual"]
theorem dual_toRightModule (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    T.dual.toRightModule = internalHom T B.regularModule := by
  exact (Dual.leftAction T).toBimodule_toRightModule

/-- The left `B`-action on `T.dual` is postcomposition by homogeneous left multiplication. -/
theorem asGradedHom_dual_leftMul (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (i p : ℤ) (b : B.X i) (f : T.dual.X p) :
    asGradedHom T B.regularModule (T.dual.leftMul i p b f) =
      cast
        (congrArg
          (fun k : ℤ ↦ DifferentialGradedModule.GradedHom
            B T.toRightModule B.regularModule k)
          (add_comm p i))
        (DifferentialGradedModule.gradedHomComp (leftMultiplication B i b)
          (asGradedHom T B.regularModule f)) := by
  have h : T.dual.leftMul = leftMul T := by
    apply eq_of_heq
    change HEq T.dual.toLeftModule.smul (leftAction T).toLeftModule.smul
    rw [show T.dual.toLeftModule = (leftAction T).toLeftModule from
      (leftAction T).toBimodule_toLeftModule]
  rw [h]
  exact asGradedHom_leftMulValue T i p b f

/-- The right `A`-action on `T.dual` is precomposition by the left `A`-action on `T`. -/
theorem dual_rightMul_apply (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (p i q : ℤ) (f : T.dual.X p) (a : A.X i) (x : T.X q) :
    asGradedHom T B.regularModule (T.dual.rightMul p i f a) q x =
      cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) (internalHomActionDegree i q p))
        ((asGradedHom T B.regularModule f) (i + q) (T.leftMul i q a x)) := by
  have h : T.dual.rightMul = (internalHom T B.regularModule).smul := by
    apply eq_of_heq
    change HEq T.dual.toRightModule.smul (internalHom T B.regularModule).smul
    rw [dual_toRightModule]
  rw [h]
  exact internalHom_smul_apply T B.regularModule p i q f a x

/-- Degree reassociation for the evaluation formula
`n tensor f ↦ (t ↦ n * f(t))`. -/
theorem evaluationDegree (p s q : ℤ) :
    p + (s + q) = s + (q + (p + 0)) := by
  omega

/-- Evaluation of a homogeneous `n : N^p` against a homogeneous dual map `f : T ⟶ B[q]`,
as a homogeneous map `T ⟶ N[q + p]`. -/
def evaluationAt (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p q : ℤ)
    (n : N.X p) (f : T.dual.X q) :
    DifferentialGradedModule.GradedHom B T.toRightModule N (q + (p + 0)) :=
  ⟨fun s ↦
      ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s)),
    by
      intro s i t b
      let f' : DifferentialGradedModule.GradedHom B T.toRightModule B.regularModule q := f
      change ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p (s + i) q))
          ((N.smul p (s + i + q) n).comp (f' (s + i)))
          (T.toRightModule.smul s i t b) =
        cast (congrArg (fun k : ℤ ↦ (N.X k : Type v))
          (DifferentialGradedModule.gradedHom_smul_index s i (q + (p + 0))))
          (N.smul (s + (q + (p + 0))) i
            (ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
              ((N.smul p (s + q) n).comp (f' s)) t) b)
      simp only [castLinearMap_apply, LinearMap.comp_apply]
      erw [f'.property s i t b]
      change cast (congrArg (fun k : ℤ ↦ (N.X k : Type v)) (evaluationDegree p (s + i) q))
        (N.smul p (s + i + q) n
          (cast (congrArg (fun k : ℤ ↦ (B.X k : Type v))
            (DifferentialGradedModule.gradedHom_smul_index s i q))
            (B.mul (s + q) i (f' s t) b))) = _
      rw [cast_smul_right N p (DifferentialGradedModule.gradedHom_smul_index s i q), N.smul_mul]
      rw [cast_smul_left N (evaluationDegree p s q) i]
      simp only [cast_cast] <;> rfl⟩

/-- Homogeneous evaluation sends `t` to the right-module product `n * f(t)`, up to the
canonical degree reassociation. -/
theorem evaluationAt_apply (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p q s : ℤ)
    (n : N.X p) (f : T.dual.X q) (t : T.X s) :
    evaluationAt T N p q n f s t =
      cast (congrArg (fun k : ℤ ↦ (N.X k : Type v)) (evaluationDegree p s q))
        (N.smul p (s + q) n ((asGradedHom T B.regularModule f) s t)) := by
  exact ModuleCat.castLinearMap_apply (congrArg N.X (evaluationDegree p s q)) _ t

/-- Fixing `n : N^p` makes evaluation a degree-`p` right-`A`-linear map from `T.dual` to
`Hom_B(T, N)`. -/
def curriedValue (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p : ℤ) (n : N.X p) :
    DifferentialGradedModule.GradedHom A T.dual.toRightModule (internalHom T N) (p + 0) :=
  ⟨fun q ↦
      { toFun := fun f ↦ evaluationAt T N p q n f
        map_add' := by
          intro f g
          apply Subtype.ext
          funext s
          change ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
              ((N.smul p (s + q) n).comp
                ((asGradedHom T B.regularModule f) s + (asGradedHom T B.regularModule g) s)) =
            ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
                ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s)) +
              ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
                ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule g) s))
          exact (congrArg (ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q)))
            (LinearMap.comp_add _ _ (N.smul p (s + q) n))).trans
            (castLinearMap_add (congrArg N.X (evaluationDegree p s q)) _ _)
        map_smul' := by
          intro r f
          apply Subtype.ext
          funext s
          change ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
              ((N.smul p (s + q) n).comp (r • (asGradedHom T B.regularModule f) s)) =
            r • ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
              ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s))
          exact (congrArg (ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q)))
            (LinearMap.comp_smul (N.smul p (s + q) n) r _)).trans
            (castLinearMap_smul (congrArg N.X (evaluationDegree p s q)) r _) },
    by
      intro q i f a
      apply Subtype.ext
      funext s
      apply LinearMap.ext
      intro t
      change evaluationAt T N p (q + i) n (T.dual.rightMul q i f a) s t =
        (cast (congrArg
          (fun k : ℤ ↦ DifferentialGradedModule.GradedHom B T.toRightModule N k)
          (DifferentialGradedModule.gradedHom_smul_index q i (p + 0)))
          ((internalHom T N).smul (q + (p + 0)) i (evaluationAt T N p q n f) a)) s t
      rw [castGradedHom_apply (DifferentialGradedModule.gradedHom_smul_index q i (p + 0))]
      erw [internalHom_smul_apply T N (q + (p + 0)) i s (evaluationAt T N p q n f) a t]
      erw [evaluationAt_apply T N p (q + i) s n (T.dual.rightMul q i f a) t]
      erw [dual_rightMul_apply T q i s f a t]
      erw [evaluationAt_apply T N p q (i + s) n f (T.leftMul i s a t)]
      rw [cast_smul_right N p (internalHomActionDegree i s q)]
      simp only [cast_cast] <;> rfl⟩

/-- Evaluation as a linear map in the first tensor factor. -/
def curriedComponent (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p : ℤ) :
    N.X p →ₗ[R] (internalHom T.dual (internalHom T N)).X (p + 0) where
  toFun := curriedValue T N p
  map_add' := by
    intro n m
    apply Subtype.ext
    funext q
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext s
    change ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        ((N.smul p (s + q) (n + m)).comp ((asGradedHom T B.regularModule f) s)) =
      ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
          ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s)) +
        ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
          ((N.smul p (s + q) m).comp ((asGradedHom T B.regularModule f) s))
    exact (congrArg (fun k : B.X (s + q) →ₗ[R] N.X (p + (s + q)) ↦
      ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        (k.comp ((asGradedHom T B.regularModule f) s)))
      ((N.smul p (s + q)).map_add n m)).trans
      (castLinearMap_add (congrArg N.X (evaluationDegree p s q))
        ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s))
        ((N.smul p (s + q) m).comp ((asGradedHom T B.regularModule f) s)))
  map_smul' := by
    intro r n
    apply Subtype.ext
    funext q
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext s
    change ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        ((N.smul p (s + q) (r • n)).comp ((asGradedHom T B.regularModule f) s)) =
      r • ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s))
    exact (congrArg (fun k : B.X (s + q) →ₗ[R] N.X (p + (s + q)) ↦
      ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        (k.comp ((asGradedHom T B.regularModule f) s)))
      ((N.smul p (s + q)).map_smul r n)).trans
      (castLinearMap_smul (congrArg N.X (evaluationDegree p s q)) r
        ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s)))

/-- The curried degree-zero map whose tensor-Hom uncurrying is the evaluation comparison. -/
def curriedEvaluation (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedModule.GradedHom B N
      (internalHom T.dual (internalHom T N)) 0 :=
  ⟨curriedComponent T N, sorry⟩

/-- Curried evaluation applies a dual map to the fixed first-factor element. -/
theorem curriedEvaluation_apply (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p q : ℤ)
    (n : N.X p) (f : T.dual.X q) :
    asGradedHom T.dual (internalHom T N) (curriedEvaluation T N p n) q f =
      evaluationAt T N p q n f := by
  rfl

/-- The closed degree-zero evaluation map
`N tensor_B T.dual ⟶ Hom_B(T, N)`. -/
@[stacks 0BZ0 "evaluation map for the dual differential graded bimodule"]
def evaluation (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedModule.ClosedGradedHom A
      (Tensor.obj N T.dual) (internalHom T N) 0 :=
  ⟨TensorHom.uncurry T.dual (curriedEvaluation T N), sorry⟩

/-- Evaluation on a pure tensor is the homogeneous map `t ↦ n * f(t)`. -/
theorem evaluation_tmul (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p q : ℤ)
    (n : N.X p) (f : T.dual.X q) :
    (evaluation T N).1 (p + q) (Tensor.tmul N T.dual n f) =
      cast
        (congrArg (fun k : ℤ ↦ ((internalHom T N).X k : Type v))
          (TensorHom.uncurryDegree p q (p + q) 0 rfl))
        (evaluationAt T N p q n f) := by
  exact TensorHom.uncurry_tmul T.dual (curriedEvaluation T N) n f

/-- Evaluation gives a natural transformation between the concrete tensor and internal-Hom
functors on closed degree-zero morphisms. -/
@[stacks 0BZ0 "tensor-dual to internal-Hom comparison on closed DG modules"]
def comparisonComp (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    (Tensor.dgFunctor T.dual).mapComp ⟶ (internalHomDgFunctor T).mapComp where
  app N := evaluation T N.obj
  naturality := sorry

/-- Evaluation gives a natural transformation between tensor and internal Hom on differential
graded homotopy categories. -/
@[stacks 0BZ0 "tensor-dual to internal-Hom comparison on DG homotopy categories"]
def comparisonK (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    (Tensor.dgFunctor T.dual).mapK ⟶ (internalHomDgFunctor T).mapK where
  app N := ((comparisonComp T).app
    (⟨N.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK
  naturality := by
    intro M N f
    refine Quotient.inductionOn f ?_
    intro g
    exact congrArg CompHom.toHomotopyClass
      ((comparisonComp T).naturality
        (X := (⟨M.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B)))
        (Y := (⟨N.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))) g)

/-- The homotopy-level comparison is represented by the explicit evaluation map. -/
theorem comparisonK_app (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : K R (DifferentialGradedModule.{u, v} B)) :
    (comparisonK T).app N = ((comparisonComp T).app
      (⟨N.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK := by
  rfl

end Dual

end DifferentialGradedBimodule
