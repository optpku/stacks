/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import ReasLib.Algebra.Module.Bimodule.TensorHom
public import ReasLib.Algebra.Module.Graded.Bimodule.InternalHom.Map
public import ReasLib.Algebra.Module.Graded.Bimodule.RelativeTensor.Map

/-!
# Graded Tensor-Hom Currying

The concrete graded relative tensor product and graded internal Hom satisfy tensor-Hom currying
in every homogeneous degree.  The degreewise equivalences assemble into an equivalence of the
canonical total graded Hom modules.  Naturality is expressed using the object maps and generic
degree-zero precomposition and postcomposition API.
-/

@[expose] public section

noncomputable section

namespace GradedModule.TensorHom

open CategoryTheory
open scoped DirectSum

universe i u v w x y z

variable {ι : Type i} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

variable (M : Right.{i, x, v, u} 𝒜)
variable (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
variable (P : Right.{i, z, w, u} 𝒝)

/-- Curry a homogeneous tensor map on one homogeneous component of its first input. -/
@[stacks 09LN "componentwise graded tensor-Hom currying"]
def curryComponent (k p : ι)
    (f : Right.HomogeneousMap (RelativeTensor.obj M N) P k) :
    M.grading p →ₗ[R] InternalHom N P where
  toFun m := InternalHom.ofHomogeneous N P (p + k)
    ⟨(Module.Bimodule.TensorHom.curry f.1 m.1).toLinearMap, sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- Curry a degree-`k` map from the canonical graded relative tensor product. -/
@[stacks 09LN "graded tensor-Hom currying"]
def curry {M : Right.{i, x, v, u} 𝒜}
    {N : Bimodule.{i, y, w, v, u} 𝒜 𝒝} {P : Right.{i, z, w, u} 𝒝} {k : ι}
    (f : Right.HomogeneousMap (RelativeTensor.obj M N) P k) :
    Right.HomogeneousMap M (InternalHom.obj N P) k :=
  ⟨{ toFun :=
        (DirectSum.toModule R ι (InternalHom N P)
          (fun p ↦ curryComponent M N P k p f)).comp
            (DirectSum.decomposeLinearEquiv M.grading).toLinearMap,
      map_add' := sorry,
      map_smul' := sorry },
    sorry⟩

/-- Uncurry a homogeneous map into the canonical graded internal-Hom object. -/
@[stacks 09LN "graded tensor-Hom uncurrying"]
def uncurry {M : Right.{i, x, v, u} 𝒜}
    {N : Bimodule.{i, y, w, v, u} 𝒜 𝒝} {P : Right.{i, z, w, u} 𝒝} {k : ι}
    (g : Right.HomogeneousMap M (InternalHom.obj N P) k) :
    Right.HomogeneousMap (RelativeTensor.obj M N) P k :=
  ⟨Module.Bimodule.TensorHom.uncurry
      (R := R) (A := A) (B := B) ((InternalHom.collapse N P).comp g.1),
    sorry⟩

/-- Tensor-Hom currying restricted to one homogeneous degree. -/
@[stacks 09LN "degreewise graded tensor-Hom adjunction"]
def degreeEquiv (k : ι) :
    Right.HomogeneousMap (RelativeTensor.obj M N) P k ≃ₗ[R]
      Right.HomogeneousMap M (InternalHom.obj N P) k where
  toFun := curry
  invFun := uncurry
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- Curried evaluation is evaluation of the original map on a pure tensor. -/
@[simp, stacks 09LN "pure-tensor formula for graded tensor-Hom currying"]
theorem curry_apply {M : Right.{i, x, v, u} 𝒜}
    {N : Bimodule.{i, y, w, v, u} 𝒜 𝒝} {P : Right.{i, z, w, u} 𝒝} {k : ι}
    (f : Right.HomogeneousMap (RelativeTensor.obj M N) P k) (m : M) (n : N) :
    InternalHom.toLinearMap N P ((curry f).1 m) n =
      f.1 (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) := sorry

/-- Uncurried evaluation on a pure tensor is evaluation in the internal Hom. -/
@[simp, stacks 09LN "pure-tensor formula for graded tensor-Hom uncurrying"]
theorem uncurry_tmul {M : Right.{i, x, v, u} 𝒜}
    {N : Bimodule.{i, y, w, v, u} 𝒜 𝒝} {P : Right.{i, z, w, u} 𝒝} {k : ι}
    (g : Right.HomogeneousMap M (InternalHom.obj N P) k) (m : M) (n : N) :
    (uncurry g).1
        (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
      InternalHom.toLinearMap N P (g.1 m) n := sorry

/-- The total graded tensor-Hom equivalence, assembled from all homogeneous degrees. -/
@[stacks 09LN "graded tensor-Hom adjunction"]
def equiv :
    Right.Hom (RelativeTensor.obj M N) P ≃ₗ[R]
      Right.Hom M (InternalHom.obj N P) :=
  DirectSum.congrLinearEquiv (fun k ↦ degreeEquiv M N P k)

/-- The total equivalence restricts on each summand to the degreewise equivalence. -/
@[simp, stacks 09LN "summand formula for the graded tensor-Hom adjunction"]
theorem equiv_of (k : ι)
    (f : Right.HomogeneousMap (RelativeTensor.obj M N) P k) :
    equiv M N P (Right.Hom.of (RelativeTensor.obj M N) P k f) =
      Right.Hom.of M (InternalHom.obj N P) k (degreeEquiv M N P k f) := sorry

/-- The inverse total graded tensor-Hom equivalence restricts on each summand to the inverse
degreewise equivalence. -/
@[simp, stacks 09LN "inverse summand formula for the graded tensor-Hom adjunction"]
theorem equiv_symm_of (k : ι)
    (g : Right.HomogeneousMap M (InternalHom.obj N P) k) :
    (equiv M N P).symm (Right.Hom.of M (InternalHom.obj N P) k g) =
      Right.Hom.of (RelativeTensor.obj M N) P k
        ((degreeEquiv M N P k).symm g) := sorry

section Naturality

variable {M M' : Right.{i, x, v, u} 𝒜}
variable {N N' : Bimodule.{i, y, w, v, u} 𝒜 𝒝}
variable {P P' : Right.{i, z, w, u} 𝒝}

/-- Degreewise currying is contravariantly natural in the first graded module. -/
theorem degreeEquiv_natural_left
    (f : Right.HomogeneousMap M' M 0) (k : ι) :
    (degreeEquiv M' N P k).toLinearMap.comp
        (Right.HomogeneousMap.precompZeroLinear (M := P) (n := k)
          (RelativeTensor.mapLeft (N := N) f)) =
      (Right.HomogeneousMap.precompZeroLinear
          (M := InternalHom.obj N P) (n := k) f).comp
        (degreeEquiv M N P k).toLinearMap := sorry

/-- Degreewise uncurrying is contravariantly natural in the first graded module. -/
theorem degreeEquiv_symm_natural_left
    (f : Right.HomogeneousMap M' M 0) (k : ι) :
    (degreeEquiv M' N P k).symm.toLinearMap.comp
        (Right.HomogeneousMap.precompZeroLinear
          (M := InternalHom.obj N P) (n := k) f) =
      (Right.HomogeneousMap.precompZeroLinear (M := P) (n := k)
          (RelativeTensor.mapLeft (N := N) f)).comp
        (degreeEquiv M N P k).symm.toLinearMap := sorry

/-- Degreewise currying is contravariantly natural in the bimodule variable. -/
theorem degreeEquiv_natural_middle (f : Bimodule.Hom N N') (k : ι) :
    (degreeEquiv M N P k).toLinearMap.comp
        (Right.HomogeneousMap.precompZeroLinear (M := P) (n := k)
          (RelativeTensor.mapRight (M := M) f)) =
      (Right.HomogeneousMap.postcompZeroLinear (K := M) (n := k)
          (InternalHom.mapSource (P := P) f)).comp
        (degreeEquiv M N' P k).toLinearMap := sorry

/-- Degreewise uncurrying is contravariantly natural in the bimodule variable. -/
theorem degreeEquiv_symm_natural_middle (f : Bimodule.Hom N N') (k : ι) :
    (degreeEquiv M N P k).symm.toLinearMap.comp
        (Right.HomogeneousMap.postcompZeroLinear (K := M) (n := k)
          (InternalHom.mapSource (P := P) f)) =
      (Right.HomogeneousMap.precompZeroLinear (M := P) (n := k)
          (RelativeTensor.mapRight (M := M) f)).comp
        (degreeEquiv M N' P k).symm.toLinearMap := sorry

/-- Degreewise currying is covariantly natural in the target graded module. -/
theorem degreeEquiv_natural_target
    (f : Right.HomogeneousMap P P' 0) (k : ι) :
    (degreeEquiv M N P' k).toLinearMap.comp
        (Right.HomogeneousMap.postcompZeroLinear
          (K := RelativeTensor.obj M N) (n := k) f) =
      (Right.HomogeneousMap.postcompZeroLinear (K := M) (n := k)
          (InternalHom.mapTarget (N := N) f)).comp
        (degreeEquiv M N P k).toLinearMap := sorry

/-- Degreewise uncurrying is covariantly natural in the target graded module. -/
theorem degreeEquiv_symm_natural_target
    (f : Right.HomogeneousMap P P' 0) (k : ι) :
    (degreeEquiv M N P' k).symm.toLinearMap.comp
        (Right.HomogeneousMap.postcompZeroLinear (K := M) (n := k)
          (InternalHom.mapTarget (N := N) f)) =
      (Right.HomogeneousMap.postcompZeroLinear
          (K := RelativeTensor.obj M N) (n := k) f).comp
        (degreeEquiv M N P k).symm.toLinearMap := sorry

/-- Degreewise currying is simultaneously natural in all three variables. -/
@[stacks 09LN "naturality of the degreewise graded tensor-Hom equivalence"]
theorem degreeEquiv_natural (f : Right.HomogeneousMap M' M 0)
    (g : Bimodule.Hom N N') (h : Right.HomogeneousMap P P' 0) (k : ι) :
    (degreeEquiv M' N P' k).toLinearMap.comp
        ((Right.HomogeneousMap.postcompZeroLinear
          (K := RelativeTensor.obj M' N) (n := k) h).comp
        (Right.HomogeneousMap.precompZeroLinear (M := P) (n := k)
          (RelativeTensor.map f g))) =
      (Right.HomogeneousMap.postcompZeroLinear (K := M') (n := k)
          (InternalHom.map g h)).comp
        ((Right.HomogeneousMap.precompZeroLinear
          (M := InternalHom.obj N' P) (n := k) f).comp
        (degreeEquiv M N' P k).toLinearMap) := sorry

/-- Degreewise uncurrying is simultaneously natural in all three variables. -/
@[stacks 09LN "inverse naturality of the degreewise graded tensor-Hom equivalence"]
theorem degreeEquiv_symm_natural (f : Right.HomogeneousMap M' M 0)
    (g : Bimodule.Hom N N') (h : Right.HomogeneousMap P P' 0) (k : ι) :
    (degreeEquiv M' N P' k).symm.toLinearMap.comp
        ((Right.HomogeneousMap.postcompZeroLinear (K := M') (n := k)
          (InternalHom.map g h)).comp
        (Right.HomogeneousMap.precompZeroLinear
          (M := InternalHom.obj N' P) (n := k) f)) =
      ((Right.HomogeneousMap.postcompZeroLinear
          (K := RelativeTensor.obj M' N) (n := k) h).comp
        (Right.HomogeneousMap.precompZeroLinear (M := P) (n := k)
          (RelativeTensor.map f g))).comp
        (degreeEquiv M N' P k).symm.toLinearMap := sorry

/-- Total graded currying is contravariantly natural in the first graded module. -/
theorem equiv_natural_left (f : Right.HomogeneousMap M' M 0) :
    (equiv M' N P).toLinearMap.comp
        (Right.Hom.precompZero (M := P) (RelativeTensor.mapLeft (N := N) f)) =
      (Right.Hom.precompZero (M := InternalHom.obj N P) f).comp
        (equiv M N P).toLinearMap := sorry

/-- Total graded uncurrying is contravariantly natural in the first graded module. -/
theorem equiv_symm_natural_left (f : Right.HomogeneousMap M' M 0) :
    (equiv M' N P).symm.toLinearMap.comp
        (Right.Hom.precompZero (M := InternalHom.obj N P) f) =
      (Right.Hom.precompZero (M := P) (RelativeTensor.mapLeft (N := N) f)).comp
        (equiv M N P).symm.toLinearMap := sorry

/-- Total graded currying is contravariantly natural in the bimodule variable. -/
theorem equiv_natural_middle (f : Bimodule.Hom N N') :
    (equiv M N P).toLinearMap.comp
        (Right.Hom.precompZero (M := P) (RelativeTensor.mapRight (M := M) f)) =
      (Right.Hom.postcompZero (K := M) (InternalHom.mapSource (P := P) f)).comp
        (equiv M N' P).toLinearMap := sorry

/-- Total graded uncurrying is contravariantly natural in the bimodule variable. -/
theorem equiv_symm_natural_middle (f : Bimodule.Hom N N') :
    (equiv M N P).symm.toLinearMap.comp
        (Right.Hom.postcompZero (K := M) (InternalHom.mapSource (P := P) f)) =
      (Right.Hom.precompZero (M := P) (RelativeTensor.mapRight (M := M) f)).comp
        (equiv M N' P).symm.toLinearMap := sorry

/-- Total graded currying is covariantly natural in the target graded module. -/
theorem equiv_natural_target (f : Right.HomogeneousMap P P' 0) :
    (equiv M N P').toLinearMap.comp
        (Right.Hom.postcompZero (K := RelativeTensor.obj M N) f) =
      (Right.Hom.postcompZero (K := M) (InternalHom.mapTarget (N := N) f)).comp
        (equiv M N P).toLinearMap := sorry

/-- Total graded uncurrying is covariantly natural in the target graded module. -/
theorem equiv_symm_natural_target (f : Right.HomogeneousMap P P' 0) :
    (equiv M N P').symm.toLinearMap.comp
        (Right.Hom.postcompZero (K := M) (InternalHom.mapTarget (N := N) f)) =
      (Right.Hom.postcompZero (K := RelativeTensor.obj M N) f).comp
        (equiv M N P).symm.toLinearMap := sorry

/-- Total graded currying is simultaneously natural in all three variables. -/
@[stacks 09LN "naturality of the graded tensor-Hom adjunction"]
theorem equiv_natural (f : Right.HomogeneousMap M' M 0)
    (g : Bimodule.Hom N N') (h : Right.HomogeneousMap P P' 0) :
    (equiv M' N P').toLinearMap.comp
        ((Right.Hom.postcompZero (K := RelativeTensor.obj M' N) h).comp
          (Right.Hom.precompZero (M := P) (RelativeTensor.map f g))) =
      (Right.Hom.postcompZero (K := M') (InternalHom.map g h)).comp
        ((Right.Hom.precompZero (M := InternalHom.obj N' P) f).comp
          (equiv M N' P).toLinearMap) := sorry

/-- Total graded uncurrying is simultaneously natural in all three variables. -/
@[stacks 09LN "inverse naturality of the graded tensor-Hom adjunction"]
theorem equiv_symm_natural (f : Right.HomogeneousMap M' M 0)
    (g : Bimodule.Hom N N') (h : Right.HomogeneousMap P P' 0) :
    (equiv M' N P').symm.toLinearMap.comp
        ((Right.Hom.postcompZero (K := M') (InternalHom.map g h)).comp
          (Right.Hom.precompZero (M := InternalHom.obj N' P) f)) =
      ((Right.Hom.postcompZero (K := RelativeTensor.obj M' N) h).comp
        (Right.Hom.precompZero (M := P) (RelativeTensor.map f g))).comp
          (equiv M N' P).symm.toLinearMap := sorry

end Naturality

namespace DegreeZero

/-- The degree-zero tensor-Hom equivalence for the fixed-bimodule functors, retaining its
`R`-linear structure. -/
@[stacks 09LN "degree-zero graded tensor-Hom linear equivalence"]
def linearEquiv (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι) :
    ((RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M ⟶ P) ≃ₗ[R]
      (M ⟶ (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P) :=
  ((Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) P.obj).symm.trans
    (degreeEquiv M.obj N P.obj 0)).trans
      (Right.degreeZeroHomEquiv M.obj (InternalHom.obj N P.obj))

/-- Degree-zero categorical currying is the degree-zero homogeneous tensor-Hom equivalence. -/
@[simp]
theorem linearEquiv_apply (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι)
    (f : (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M ⟶ P) :
    linearEquiv.{i, u, v, w, x, y} N M P f =
      Right.degreeZeroHomEquiv M.obj (InternalHom.obj N P.obj)
        (degreeEquiv M.obj N P.obj 0
          ((Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) P.obj).symm f)) := sorry

/-- Degree-zero categorical uncurrying is the inverse degree-zero homogeneous tensor-Hom
equivalence. -/
@[simp]
theorem linearEquiv_symm_apply (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι)
    (g : M ⟶ (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P) :
    (linearEquiv.{i, u, v, w, x, y} N M P).symm g =
      Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) P.obj
        ((degreeEquiv M.obj N P.obj 0).symm
          ((Right.degreeZeroHomEquiv M.obj (InternalHom.obj N P.obj)).symm g)) := sorry

/-- The plain Hom equivalence underlying degree-zero graded tensor-Hom currying. -/
def homEquiv (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι) :
    ((RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M ⟶ P) ≃
      (M ⟶ (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P) :=
  (linearEquiv.{i, u, v, w, x, y} N M P).toEquiv

/-- Plain degree-zero categorical currying is the underlying map of the linear equivalence. -/
@[simp]
theorem homEquiv_apply (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι)
    (f : (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M ⟶ P) :
    homEquiv.{i, u, v, w, x, y} N M P f =
      linearEquiv.{i, u, v, w, x, y} N M P f := sorry

/-- Plain degree-zero categorical uncurrying is the underlying inverse of the linear
equivalence. -/
@[simp]
theorem homEquiv_symm_apply (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι)
    (g : M ⟶ (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P) :
    (homEquiv.{i, u, v, w, x, y} N M P).symm g =
      (linearEquiv.{i, u, v, w, x, y} N M P).symm g := sorry

/-- The degree-zero Hom equivalence is contravariantly natural in its first right graded
module. -/
theorem homEquiv_naturality_left_symm (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    {M' M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι}
    {P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι}
    (f : M' ⟶ M)
    (g : M ⟶ (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P) :
    (homEquiv.{i, u, v, w, x, y} N M' P).symm (f ≫ g) =
      (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).map f ≫
        (homEquiv.{i, u, v, w, x, y} N M P).symm g := sorry

/-- The degree-zero Hom equivalence is covariantly natural in its target right graded module. -/
theorem homEquiv_naturality_right (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    {M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι}
    {P P' : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι}
    (f : (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M ⟶ P)
    (g : P ⟶ P') :
    homEquiv.{i, u, v, w, x, y} N M P' (f ≫ g) =
      homEquiv.{i, u, v, w, x, y} N M P f ≫
        (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).map g := sorry

/-- The degree-zero tensor-Hom equivalence is contravariantly natural in the graded bimodule
parameter. -/
@[stacks 09LN "naturality of the graded tensor-Hom adjunction in the bimodule"]
theorem homEquiv_naturality_middle {N N' : Bimodule.{i, y, w, v, u} 𝒜 𝒝}
    (f : N ⟶ N')
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι)
    (g : (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N').obj M ⟶ P) :
    homEquiv.{i, u, v, w, x, y} N M P
        ((RelativeTensor.DegreeZero.map.{i, u, v, w, x, y} f).app M ≫ g) =
      homEquiv.{i, u, v, w, x, y} N' M P g ≫
        (InternalHom.DegreeZero.map.{i, u, v, w, y, x} f).app P := sorry

/-- Tensoring with a fixed graded bimodule is left adjoint to fixed-source graded internal Hom
on the canonical degree-zero categories. -/
@[stacks 09LN "degree-zero graded tensor-Hom adjunction"]
def adjunction (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N ⊣
      InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv.{i, u, v, w, x, y} N
      homEquiv_naturality_left_symm :=
        homEquiv_naturality_left_symm.{i, u, v, w, x, y} N
      homEquiv_naturality_right :=
        homEquiv_naturality_right.{i, u, v, w, x, y} N }

/-- The explicit internal-Hom transformation induced by a graded bimodule morphism is the
mate of the corresponding relative tensor transformation. -/
@[stacks 09LN "mate compatibility of graded tensor and internal Hom"]
theorem internalHomMap_eq_conjugateEquiv
    {N N' : Bimodule.{i, y, w, v, u} 𝒜 𝒝} (f : N ⟶ N') :
    InternalHom.DegreeZero.map.{i, u, v, w, y, x} f =
      conjugateEquiv (adjunction.{i, u, v, w, x, y} N')
        (adjunction.{i, u, v, w, x, y} N)
        (RelativeTensor.DegreeZero.map.{i, u, v, w, x, y} f) := sorry

/-- The Hom equivalences of the fixed-bimodule adjunctions are natural in their shared graded
bimodule parameter, expressed through the bundled parameter functors. -/
theorem homEquiv_naturality_parameter
    {N N' : Bimodule.{i, y, w, v, u} 𝒜 𝒝} (f : N ⟶ N')
    {M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι}
    {P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι}
    (g : ((RelativeTensor.DegreeZero.bimoduleFunctor.{i, u, v, w, x, y}
      (𝒜 := 𝒜) (𝒝 := 𝒝)).obj N').obj M ⟶ P) :
    (adjunction.{i, u, v, w, x, y} N).homEquiv M P
        (((RelativeTensor.DegreeZero.bimoduleFunctor.{i, u, v, w, x, y}
          (𝒜 := 𝒜) (𝒝 := 𝒝)).map f).app M ≫ g) =
      (adjunction.{i, u, v, w, x, y} N').homEquiv M P g ≫
        ((InternalHom.DegreeZero.bimoduleFunctor.{i, u, v, w, y, x}
          (𝒜 := 𝒜) (𝒝 := 𝒝)).map f.op).app P := sorry

/-- The graded relative tensor and internal-Hom bifunctors form a Mathlib-style adjunction
with the graded bimodule as parameter. -/
@[stacks 09LN "parametrized graded tensor-Hom adjunction"]
def parametrizedAdjunction :
    RelativeTensor.DegreeZero.bimoduleFunctor.{i, u, v, w, x, y}
        (𝒜 := 𝒜) (𝒝 := 𝒝) ⊣₂
      InternalHom.DegreeZero.bimoduleFunctor.{i, u, v, w, y, x}
        (𝒜 := 𝒜) (𝒝 := 𝒝) :=
  ParametrizedAdjunction.mk'
    (fun N => adjunction.{i, u, v, w, x, y} N)
    (fun {N N'} f {M} {P} g =>
      homEquiv_naturality_parameter.{i, u, v, w, x, y}
        (N := N) (N' := N') f (M := M) (P := P) g)

/-- The adjunction at a graded bimodule parameter is the fixed-bimodule tensor-Hom
adjunction. -/
@[simp]
theorem parametrizedAdjunction_adj
    (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (parametrizedAdjunction.{i, u, v, w, x, y}
      (𝒜 := 𝒜) (𝒝 := 𝒝)).adj N = adjunction.{i, u, v, w, x, y} N := sorry

/-- The fixed-bimodule relative tensor functor is recognized as a left adjoint. -/
instance tensorIsLeftAdjoint (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).IsLeftAdjoint := sorry

/-- The fixed-source internal-Hom functor is recognized as a right adjoint. -/
instance internalHomIsRightAdjoint (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).IsRightAdjoint := sorry

/-- The Hom equivalence of the degree-zero adjunction is categorical tensor-Hom currying. -/
@[simp]
theorem adjunction_homEquiv (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι) :
    (adjunction.{i, u, v, w, x, y} N).homEquiv M P =
      homEquiv.{i, u, v, w, x, y} N M P := sorry

/-- The degree-zero adjunction unit is currying of the identity tensor morphism. -/
theorem adjunction_unit_app (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι) :
    (adjunction.{i, u, v, w, x, y} N).unit.app M =
      homEquiv.{i, u, v, w, x, y} N M
        ((RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M)
        (𝟙 ((RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).obj M)) := sorry

/-- The degree-zero adjunction counit is uncurrying of the identity internal-Hom morphism. -/
theorem adjunction_counit_app (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), w, u} 𝒝) ι) :
    (adjunction.{i, u, v, w, x, y} N).counit.app P =
      (homEquiv.{i, u, v, w, x, y} N
        ((InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P) P).symm
          (𝟙 ((InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).obj P)) := sorry

end DegreeZero

#synth (RelativeTensor.DegreeZero.functor.{i, u, v, w, x, y} N).IsLeftAdjoint
#synth (InternalHom.DegreeZero.functor.{i, u, v, w, y, x} N).IsRightAdjoint

end GradedModule.TensorHom
