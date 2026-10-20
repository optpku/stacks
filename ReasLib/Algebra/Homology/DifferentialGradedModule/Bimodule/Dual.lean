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

/-- Left multiplication by a homogeneous element of `B`, as a homogeneous endomorphism of the
regular right `B`-module. -/
def leftMultiplication (B : CochainDGAlgebra.{u, v} R) (i : ℤ) (b : B.X i) :
    DifferentialGradedModule.GradedHom B B.regularModule B.regularModule i :=
  ⟨fun p ↦ ModuleCat.castLinearMap (congrArg B.X (add_comm i p)) (B.mul i p b), sorry⟩

/-- Homogeneous left multiplication on the regular module evaluates as multiplication in `B`.
-/
theorem leftMultiplication_apply (B : CochainDGAlgebra.{u, v} R) (i p : ℤ)
    (b : B.X i) (x : B.X p) :
    leftMultiplication B i b p x =
      cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) (add_comm i p))
        (B.mul i p b x) := sorry

/-- Postcomposition by left multiplication, with the output degree reordered for a left
`B`-action on `Hom_B(T, B)`. -/
def leftMulValue (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (i p : ℤ) (b : B.X i) (f : (internalHom T B.regularModule).X p) :
    (internalHom T B.regularModule).X (i + p) :=
  cast
    (congrArg (fun n : ℤ ↦ ((internalHom T B.regularModule).X n : Type v))
      (add_comm p i))
    (internalHomMap T (leftMultiplication B i b) p f)

/-- Postcomposition by left multiplication is bilinear in the algebra element and the
internal-Hom element. -/
def leftMul (T : DifferentialGradedBimodule.{u, v, v, v} A B) (i p : ℤ) :
    B.X i →ₗ[R] (internalHom T B.regularModule).X p →ₗ[R]
      (internalHom T B.regularModule).X (i + p) where
  toFun := fun b ↦
    { toFun := leftMulValue T i p b
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The compatible left `B`-action on `Hom_B(T, B)` obtained by homogeneous
postcomposition. -/
def leftAction (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    LeftAction B (internalHom T B.regularModule) where
  leftMul := leftMul T
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
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
          (asGradedHom T B.regularModule f)) := sorry

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
    T.dual.toRightModule = internalHom T B.regularModule := sorry

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
          (asGradedHom T B.regularModule f)) := sorry

/-- The right `A`-action on `T.dual` is precomposition by the left `A`-action on `T`. -/
theorem dual_rightMul_apply (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (p i q : ℤ) (f : T.dual.X p) (a : A.X i) (x : T.X q) :
    asGradedHom T B.regularModule (T.dual.rightMul p i f a) q x =
      cast (congrArg (fun n : ℤ ↦ (B.X n : Type v)) (internalHomActionDegree i q p))
        ((asGradedHom T B.regularModule f) (i + q) (T.leftMul i q a x)) := sorry

/-- Degree reassociation for the evaluation formula
`n tensor f ↦ (t ↦ n * f(t))`. -/
theorem evaluationDegree (p s q : ℤ) :
    p + (s + q) = s + (q + (p + 0)) := sorry

/-- Evaluation of a homogeneous `n : N^p` against a homogeneous dual map `f : T ⟶ B[q]`,
as a homogeneous map `T ⟶ N[q + p]`. -/
def evaluationAt (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p q : ℤ)
    (n : N.X p) (f : T.dual.X q) :
    DifferentialGradedModule.GradedHom B T.toRightModule N (q + (p + 0)) :=
  ⟨fun s ↦
      ModuleCat.castLinearMap (congrArg N.X (evaluationDegree p s q))
        ((N.smul p (s + q) n).comp ((asGradedHom T B.regularModule f) s)),
    sorry⟩

/-- Homogeneous evaluation sends `t` to the right-module product `n * f(t)`, up to the
canonical degree reassociation. -/
theorem evaluationAt_apply (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p q s : ℤ)
    (n : N.X p) (f : T.dual.X q) (t : T.X s) :
    evaluationAt T N p q n f s t =
      cast (congrArg (fun k : ℤ ↦ (N.X k : Type v)) (evaluationDegree p s q))
        (N.smul p (s + q) n ((asGradedHom T B.regularModule f) s t)) := sorry

/-- Fixing `n : N^p` makes evaluation a degree-`p` right-`A`-linear map from `T.dual` to
`Hom_B(T, N)`. -/
def curriedValue (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p : ℤ) (n : N.X p) :
    DifferentialGradedModule.GradedHom A T.dual.toRightModule (internalHom T N) (p + 0) :=
  ⟨fun q ↦
      { toFun := fun f ↦ evaluationAt T N p q n f
        map_add' := sorry
        map_smul' := sorry },
    sorry⟩

/-- Evaluation as a linear map in the first tensor factor. -/
def curriedComponent (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : DifferentialGradedModule.{u, v} B) (p : ℤ) :
    N.X p →ₗ[R] (internalHom T.dual (internalHom T N)).X (p + 0) where
  toFun := curriedValue T N p
  map_add' := sorry
  map_smul' := sorry

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
      evaluationAt T N p q n f := sorry

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
        (evaluationAt T N p q n f) := sorry

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
  naturality := sorry

/-- The homotopy-level comparison is represented by the explicit evaluation map. -/
theorem comparisonK_app (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (N : K R (DifferentialGradedModule.{u, v} B)) :
    (comparisonK T).app N = ((comparisonComp T).app
      (⟨N.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK := sorry

end Dual

end DifferentialGradedBimodule
