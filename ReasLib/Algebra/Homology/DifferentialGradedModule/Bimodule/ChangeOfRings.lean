/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Unit
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Ulift

/-!
# Extension-of-Scalars Bimodules

A DGA homomorphism `f : A ⟶ B` makes the regular right `B`-module into an `(A, B)`-bimodule.
This is the canonical kernel for tensor extension of scalars.  Keeping it as a named owner avoids
reconstructing the left action in each base-change or restriction argument.
-/

@[expose] public section

noncomputable section

universe u a b v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.ChangeOfRings

variable {R : Type u} [CommRing R]

section Heterogeneous

variable {A : CochainDGAlgebra.{u, a} R}
variable {B : CochainDGAlgebra.{u, b} R}

/-- The regular `B`-module transported to the common carrier universe `max a b`. -/
@[stacks 0BYZ "universe-lifted regular target module for extension of scalars"]
abbrev uliftRegular (B : CochainDGAlgebra.{u, b} R) :
    DifferentialGradedModule.{u, max a b} B :=
  DifferentialGradedModule.ulift.{u, b, b, a} B.regularModule

/-- The regular target multiplication after applying a DGA homomorphism. -/
@[stacks 0BYZ "heterogeneous extension-of-scalars multiplication"]
def extensionMulBase (f : CochainDGAlgebra.Hom A B) (i p : ℤ) :
    A.X i →ₗ[R] B.X p →ₗ[R] B.X (i + p) :=
  (B.mul i p).comp (f.map i)

/-- The left action on the universe-lifted regular target module. -/
@[stacks 0BYZ "heterogeneous extension-of-scalars left action"]
def extensionUliftMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ) :
    A.X i →ₗ[R] (uliftRegular.{u, a, b} B).X p →ₗ[R]
      (uliftRegular.{u, a, b} B).X (i + p) :=
  DifferentialGradedModule.uliftRightSmul.{u, a, b, a}
    (extensionMulBase f i p)

/-- A compatible left `A`-action on the universe-lifted regular right `B`-module. -/
@[stacks 0BYZ "heterogeneous extension-of-scalars compatible action"]
def extensionUliftAction (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.LeftAction A (uliftRegular.{u, a, b} B) where
  leftMul := extensionUliftMul f
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- Extension of scalars for DGAs with independent carrier universes. -/
@[stacks 0BYZ "heterogeneous extension-of-scalars differential graded bimodule"]
def extensionUlift (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.{u, max a b, a, b} A B :=
  (extensionUliftAction f).toBimodule

/-- The universe-lifted extension action evaluates by multiplying in `B`. -/
@[simp 1100, stacks 0BYZ "heterogeneous extension-of-scalars action formula"]
theorem extensionUlift_leftMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ)
    (a : A.X i) (b : (extensionUlift f).X p) :
    (extensionUlift f).leftMul i p a b =
      ULift.up (B.mul i p (f i a) b.down) := sorry

/-- The right module underlying heterogeneous extension of scalars. -/
@[simp, stacks 0BYZ "heterogeneous extension-of-scalars right-module formula"]
theorem extensionUlift_toRightModule (f : CochainDGAlgebra.Hom A B) :
    (extensionUlift f).toRightModule = uliftRegular.{u, a, b} B := sorry

/-- The complex underlying heterogeneous extension of scalars. -/
@[simp, stacks 0BYZ "heterogeneous extension-of-scalars complex formula"]
theorem extensionUlift_toCochainComplex (f : CochainDGAlgebra.Hom A B) :
    (extensionUlift f).toCochainComplex =
      (uliftRegular.{u, a, b} B).toCochainComplex := sorry

/-- The restricted regular module transported to the common carrier universe `max a b`. -/
@[stacks 09LD "universe-lifted restricted target module"]
abbrev uliftRestricted (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedModule.{u, max a b} A :=
  DifferentialGradedModule.ulift.{u, b, a, a} (f.restrictModule B.regularModule)

/-- The regular `B`-multiplication on the universe-lifted restricted module. -/
@[stacks 09LD "heterogeneous restriction-of-scalars multiplication"]
def restrictionUliftMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ) :
    B.X i →ₗ[R] (uliftRestricted.{u, a, b} f).X p →ₗ[R]
      (uliftRestricted.{u, a, b} f).X (i + p) :=
  DifferentialGradedModule.uliftRightSmul.{u, b, b, a} (B.mul i p)

/-- A compatible left `B`-action on the universe-lifted restricted regular module. -/
@[stacks 09LD "heterogeneous restriction-of-scalars compatible action"]
def restrictionUliftAction (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.LeftAction B (uliftRestricted.{u, a, b} f) where
  leftMul := restrictionUliftMul f
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- Restriction of scalars for DGAs with independent carrier universes. -/
@[stacks 09LD "heterogeneous restriction-of-scalars differential graded bimodule"]
def restrictionUlift (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.{u, max a b, b, a} B A :=
  (restrictionUliftAction f).toBimodule

/-- The universe-lifted restriction action evaluates by multiplication in `B`. -/
@[simp 1100, stacks 09LD "heterogeneous restriction-of-scalars action formula"]
theorem restrictionUlift_leftMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ)
    (b : B.X i) (x : (restrictionUlift f).X p) :
    (restrictionUlift f).leftMul i p b x = ULift.up (B.mul i p b x.down) := sorry

/-- The right module underlying heterogeneous restriction of scalars. -/
@[simp, stacks 09LD "heterogeneous restriction-of-scalars right-module formula"]
theorem restrictionUlift_toRightModule (f : CochainDGAlgebra.Hom A B) :
    (restrictionUlift f).toRightModule = uliftRestricted.{u, a, b} f := sorry

/-- The complex underlying heterogeneous restriction of scalars. -/
@[simp, stacks 09LD "heterogeneous restriction-of-scalars complex formula"]
theorem restrictionUlift_toCochainComplex (f : CochainDGAlgebra.Hom A B) :
    (restrictionUlift f).toCochainComplex =
      (uliftRestricted.{u, a, b} f).toCochainComplex := sorry

end Heterogeneous

section MaxTarget

variable {A : CochainDGAlgebra.{u, a} R}
variable {B : CochainDGAlgebra.{u, max a b} R}

/-- The left action induced on the regular right `B`-module by a DGA homomorphism `f : A ⟶ B`. -/
@[stacks 0BYZ "extension-of-scalars left action"]
def extensionMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ) :
    A.X i →ₗ[R] B.regularModule.X p →ₗ[R] B.regularModule.X (i + p) :=
  (B.mul i p).comp (f.map i)

/-- The compatible left `A`-action on the regular right `B`-module induced by `f : A ⟶ B`. -/
@[stacks 0BYZ "extension-of-scalars compatible action"]
def extensionAction (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.LeftAction A B.regularModule where
  leftMul := extensionMul f
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- The canonical `(A, B)`-bimodule associated to a DGA homomorphism `f : A ⟶ B`. -/
@[stacks 0BYZ "extension-of-scalars differential graded bimodule"]
def extension (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.{u, max a b, a, max a b} A B :=
  (extensionAction f).toBimodule

/-- The induced left action is multiplication after applying the DGA homomorphism. -/
@[simp 1100, stacks 0BYZ "extension-of-scalars action formula"]
theorem extension_leftMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ)
    (a : A.X i) (b : B.X p) :
    (extension f).leftMul i p a b = B.mul i p (f i a) b := sorry

/-- The right module underlying an extension-of-scalars bimodule is the regular target module. -/
@[simp, stacks 0BYZ "extension-of-scalars right-module formula"]
theorem extension_toRightModule (f : CochainDGAlgebra.Hom A B) :
    (extension f).toRightModule = B.regularModule := sorry

/-- The complex underlying an extension-of-scalars bimodule is the target DGA complex. -/
@[simp, stacks 0BYZ "extension-of-scalars complex formula"]
theorem extension_toCochainComplex (f : CochainDGAlgebra.Hom A B) :
    (extension f).toCochainComplex = B.toCochainComplex := sorry

/-- Left multiplication on `B`, viewed on the restriction of its regular module along
`f : A ⟶ B`. -/
@[stacks 09LD "restriction-of-scalars left action"]
def restrictionMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ) :
    B.X i →ₗ[R] (f.restrictModule B.regularModule).X p →ₗ[R]
      (f.restrictModule B.regularModule).X (i + p) :=
  B.mul i p

/-- The regular left `B`-action on the regular module restricted on the right along
`f : A ⟶ B`. -/
@[stacks 09LD "restriction-of-scalars compatible action"]
def restrictionAction (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.LeftAction B (f.restrictModule B.regularModule) where
  leftMul := restrictionMul f
  left_assoc := sorry
  one_left := sorry
  comm_right := sorry
  d_leftMul := sorry

/-- The canonical `(B, A)`-bimodule which represents restriction of scalars along
`f : A ⟶ B` by relative tensor product. -/
@[stacks 09LD "restriction-of-scalars differential graded bimodule"]
def restriction (f : CochainDGAlgebra.Hom A B) :
    DifferentialGradedBimodule.{u, max a b, max a b, a} B A :=
  (restrictionAction f).toBimodule

/-- The left action on the restriction bimodule is regular multiplication in `B`. -/
@[simp 1100, stacks 09LD "restriction-of-scalars action formula"]
theorem restriction_leftMul (f : CochainDGAlgebra.Hom A B) (i p : ℤ)
    (b : B.X i) (x : B.X p) :
    (restriction f).leftMul i p b x = B.mul i p b x := sorry

/-- The right module underlying the restriction bimodule is the regular target module with
scalars restricted along `f`. -/
@[simp, stacks 09LD "restriction-of-scalars right-module formula"]
theorem restriction_toRightModule (f : CochainDGAlgebra.Hom A B) :
    (restriction f).toRightModule = f.restrictModule B.regularModule := sorry

/-- The complex underlying a restriction bimodule is the target DGA complex. -/
@[simp, stacks 09LD "restriction-of-scalars complex formula"]
theorem restriction_toCochainComplex (f : CochainDGAlgebra.Hom A B) :
    (restriction f).toCochainComplex = B.toCochainComplex := sorry

end MaxTarget

section SameCarrier

variable {A B : CochainDGAlgebra.{u, v} R}

/-- Evaluate a homogeneous right-`B`-linear map from the extension bimodule at `1 ∈ B`. -/
def evalOneValue (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ)
    (g : (internalHom (extension.{u, v, 0} f) P).X k) : (f.restrictModule P).X k :=
  cast (congrArg (fun n : ℤ ↦ (P.X n : Type v)) (zero_add k))
    (asGradedHom (extension.{u, v, 0} f) P g 0 B.one)

/-- Evaluation at one is linear in each homogeneous degree. -/
def evalOneLinear (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (internalHom (extension.{u, v, 0} f) P).X k →ₗ[R] (f.restrictModule P).X k where
  toFun := evalOneValue f P k
  map_add' := sorry
  map_smul' := sorry

/-- Evaluation at one as a morphism of right differential graded `A`-modules. -/
def evalOne (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) :
    internalHom (extension.{u, v, 0} f) P ⟶ f.restrictModule P where
  hom := evalOneLinear f P
  comm_d := sorry
  comm_smul := sorry

/-- A homogeneous element defines a homogeneous right-`B`-linear map from `B` by right
multiplication. -/
def fromValueGradedHom (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ)
    (x : (f.restrictModule P).X k) :
    DifferentialGradedModule.GradedHom B (extension.{u, v, 0} f).toRightModule P k :=
  ⟨fun n ↦
      { toFun := fun b ↦
          cast (congrArg (fun i : ℤ ↦ (P.X i : Type v)) (add_comm k n))
            (P.smul k n x b)
        map_add' := sorry
        map_smul' := sorry },
    sorry⟩

/-- The right-multiplication construction is linear in the chosen homogeneous element. -/
def fromValueLinear (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (f.restrictModule P).X k →ₗ[R] (internalHom (extension.{u, v, 0} f) P).X k where
  toFun := fromValueGradedHom f P k
  map_add' := sorry
  map_smul' := sorry

/-- Right multiplication as the inverse morphism to evaluation at one. -/
def fromValue (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) :
    f.restrictModule P ⟶ internalHom (extension.{u, v, 0} f) P where
  hom := fromValueLinear f P
  comm_d := sorry
  comm_smul := sorry

/-- Example 22.33.6 (0BYX) (1): evaluation at `1 ∈ B` identifies internal Hom from the
extension bimodule with restriction of scalars. -/
@[stacks 0BYX "evaluation at one for a DGA homomorphism"]
def evalOneIso (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) :
    internalHom (extension.{u, v, 0} f) P ≅ f.restrictModule P where
  hom := evalOne f P
  inv := fromValue f P
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Evaluation at one is the degree-zero value of the represented homogeneous map. -/
@[simp, stacks 0BYX "evaluation-at-one component formula"]
theorem evalOne_apply (f : CochainDGAlgebra.Hom A B)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ)
    (g : (internalHom (extension.{u, v, 0} f) P).X k) :
    (evalOne f P).hom k g = evalOneValue f P k g := sorry

/-- Evaluation at one is natural on homotopy categories. -/
@[stacks 0BYX "evaluation-at-one homotopy component"]
def evalOneMapKIsoApp (f : CochainDGAlgebra.Hom A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    ((internalHomDgFunctor (extension.{u, v, 0} f)).mapK).obj P ≅
      (f.restrictDgFunctor.mapK).obj P :=
  (DifferentialGradedModule.toK A).mapIso (evalOneIso f P.obj)

/-- Evaluation at one is natural on homotopy categories. -/
@[stacks 0BYX "evaluation at one on homotopy categories"]
def evalOneMapKIso (f : CochainDGAlgebra.Hom A B) :
    (internalHomDgFunctor (extension.{u, v, 0} f)).mapK ≅ f.restrictDgFunctor.mapK :=
  NatIso.ofComponents
    (evalOneMapKIsoApp f)
    (fun _ ↦ sorry)

/-- The forward component of evaluation at one is the pointwise evaluation isomorphism. -/
@[simp, stacks 0BYX "forward evaluation-at-one homotopy component"]
theorem evalOneMapKIso_hom_app (f : CochainDGAlgebra.Hom A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    (evalOneMapKIso f).hom.app P = Iso.hom (evalOneMapKIsoApp f P) := sorry

/-- The inverse component of evaluation at one is the pointwise inverse isomorphism. -/
@[simp, stacks 0BYX "inverse evaluation-at-one homotopy component"]
theorem evalOneMapKIso_inv_app (f : CochainDGAlgebra.Hom A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    (evalOneMapKIso f).inv.app P = Iso.inv (evalOneMapKIsoApp f P) := sorry

/-- The left module underlying the restriction bimodule is the regular left `B`-module. -/
def restrictionLeftIso (f : CochainDGAlgebra.Hom A B) :
    (restriction.{u, v, 0} f).toLeftModule ≅ B.leftRegularModule where
  hom :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  inv :=
    { hom := fun _ ↦ LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Evaluation of `M ⊗_B {}_B B_A` by the right `B`-action, before repackaging the target
as a restricted right `A`-module. -/
def restrictionTensorEvaluationComplex (f : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedModule.TensorProduct.complex M (restriction.{u, v, 0} f).toLeftModule ⟶
      M.toCochainComplex :=
  DifferentialGradedModule.TensorProduct.mapLeft M (restrictionLeftIso f).hom ≫
    DifferentialGradedModule.TensorProduct.rightRegularEvaluation M

/-- Insert `1 ∈ B` in the second factor of `M ⊗_B {}_B B_A`. -/
def restrictionTensorCoevaluationComplex (f : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B) :
    M.toCochainComplex ⟶
      DifferentialGradedModule.TensorProduct.complex M (restriction.{u, v, 0} f).toLeftModule :=
  DifferentialGradedModule.TensorProduct.rightRegularCoevaluation M ≫
    DifferentialGradedModule.TensorProduct.mapLeft M (restrictionLeftIso f).inv

/-- Evaluation of the restriction bimodule tensor product as a right DG `A`-module map. -/
def restrictionTensorEvaluation (f : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B) :
    Tensor.obj M (restriction.{u, v, 0} f) ⟶ f.restrictModule M where
  hom n := ((restrictionTensorEvaluationComplex f M).f n).hom
  comm_d := sorry
  comm_smul := sorry

/-- Unit insertion into the restriction bimodule tensor product as a right DG `A`-module map. -/
def restrictionTensorCoevaluation (f : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B) :
    f.restrictModule M ⟶ Tensor.obj M (restriction.{u, v, 0} f) where
  hom n := ((restrictionTensorCoevaluationComplex f M).f n).hom
  comm_d := sorry
  comm_smul := sorry

/-- Example 22.33.6 (0BYX) (4): restriction of scalars is tensoring with the canonical
`(B, A)`-bimodule `{}_B B_A`. -/
@[stacks 0BYX "restriction of scalars as tensoring with the regular bimodule"]
def restrictionTensorIso (f : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B) :
    Tensor.obj M (restriction.{u, v, 0} f) ≅ f.restrictModule M where
  hom := restrictionTensorEvaluation f M
  inv := restrictionTensorCoevaluation f M
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction-tensor evaluation sends a pure tensor to the right module action. -/
@[stacks 0BYX "restriction-tensor evaluation on pure tensors"]
theorem restrictionTensorEvaluation_tmul (f : CochainDGAlgebra.Hom A B)
    (M : DifferentialGradedModule.{u, v} B) (p q : ℤ)
    (x : M.X p) (b : B.X q) :
    (restrictionTensorEvaluation f M).hom (p + q)
        (Tensor.tmul M (restriction.{u, v, 0} f) x b) = M.smul p q x b := sorry

/-- The tensor presentation of restriction is natural on homotopy categories. -/
@[stacks 0BYX "restriction-tensor homotopy component"]
def restrictionTensorMapKIsoApp (f : CochainDGAlgebra.Hom A B)
    (M : K R (DifferentialGradedModule.{u, v} B)) :
    ((Tensor.dgFunctor (restriction.{u, v, 0} f)).mapK).obj M ≅
      (f.restrictDgFunctor.mapK).obj M :=
  (DifferentialGradedModule.toK A).mapIso (restrictionTensorIso f M.obj)

/-- The tensor presentation of restriction is natural on homotopy categories. -/
@[stacks 0BYX "restriction tensor presentation on homotopy categories"]
def restrictionTensorMapKIso (f : CochainDGAlgebra.Hom A B) :
    (Tensor.dgFunctor (restriction.{u, v, 0} f)).mapK ≅ f.restrictDgFunctor.mapK :=
  NatIso.ofComponents
    (restrictionTensorMapKIsoApp f)
    (fun _ ↦ sorry)

/-- The forward component of the restriction-tensor presentation is pointwise evaluation. -/
@[simp, stacks 0BYX "forward restriction-tensor homotopy component"]
theorem restrictionTensorMapKIso_hom_app (f : CochainDGAlgebra.Hom A B)
    (M : K R (DifferentialGradedModule.{u, v} B)) :
    (restrictionTensorMapKIso f).hom.app M =
      Iso.hom (restrictionTensorMapKIsoApp f M) := sorry

/-- The inverse component of the restriction-tensor presentation is pointwise coevaluation. -/
@[simp, stacks 0BYX "inverse restriction-tensor homotopy component"]
theorem restrictionTensorMapKIso_inv_app (f : CochainDGAlgebra.Hom A B)
    (M : K R (DifferentialGradedModule.{u, v} B)) :
    (restrictionTensorMapKIso f).inv.app M =
      Iso.inv (restrictionTensorMapKIsoApp f M) := sorry

end SameCarrier

end DifferentialGradedBimodule.ChangeOfRings
