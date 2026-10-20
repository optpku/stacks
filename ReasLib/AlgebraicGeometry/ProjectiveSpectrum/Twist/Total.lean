/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Total
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Reindex
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation

/-!
# Total twist algebras

This file defines explicit presentations of the integral and nonnegative total twist algebras
on a projective spectrum, together with their comparison map.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjSpec

/-- The naturally graded algebra formed by restricting an integral twist algebra to
nonnegative degrees. -/
noncomputable def nonnegativeTwistAlgebra (A : Scheme.Hom.AbsoluteProjModel)
    (twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst) :
    SheafOfModules.RingedSite.GradedAlgebraSheaf A.proj.sheaf ℕ :=
  SheafOfModules.RingedSite.GradedAlgebraSheaf.reindex
    (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst twists)
    Int.ofNatHom.toAddMonoidHom

/-- The naturally graded family formed by the nonnegative twists of an integral twist
algebra. -/
def nonnegativeTwists (A : Scheme.Hom.AbsoluteProjModel)
    (twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst) : GradedObject ℕ A.proj.Modules :=
  fun n : ℕ ↦
    @ProjTwistAlgebra.actualTwist A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst twists (n : ℤ)

/-- Explicit algebra presentations of the integral and nonnegative sums of twists on
`Proj(A)`. -/
structure TwistTotals (A : Scheme.Hom.AbsoluteProjModel)
    (twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst) where
  /-- The quasi-coherent algebra `⊕ (m : ℤ), 𝒪(m)`. -/
  integer : A.proj.QcAlgebraUnder
  /-- The quasi-coherent algebra `⊕ (m : ℕ), 𝒪(m)`. -/
  nonnegative : A.proj.QcAlgebraUnder
  /-- The inclusion of the nonnegative sum into the integral sum. -/
  inclusion : nonnegative ⟶ integer
  /-- The underlying module of the integral algebra is the direct sum of all twists. -/
  integerIso :
    (GradedObject.Total.functor (I := ℤ) (C := A.proj.Modules)).obj
        (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject ≅
      Scheme.QcAlgebraUnder.underlyingModule A.proj integer
  /-- The underlying module of the nonnegative algebra is the direct sum of the nonnegative
  twists. -/
  nonnegativeIso :
    (GradedObject.Total.functor (I := ℕ) (C := A.proj.Modules)).obj
        (nonnegativeTwists A twists) ≅
      Scheme.QcAlgebraUnder.underlyingModule A.proj nonnegative
  /-- The integral direct-sum presentation carries the degree-zero twist unit to the unit of
  the presented algebra. -/
  integer_one : ∀ U : (A.proj.Opens)ᵒᵖ,
    (((Sigma.ι
        (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
        0 ≫ integerIso.hom).val.app U).hom
      ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
        A.gradeAddSubgroupClass A.grading A.grading_inst twists).one U) :
      (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U) =
      (1 : (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U)
  /-- The integral direct-sum presentation carries homogeneous twist multiplication to
  multiplication in the presented algebra. -/
  integer_mul : ∀ (U : (A.proj.Opens)ᵒᵖ) (a b : ℤ)
      (x : ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
        A.gradeAddSubgroupClass A.grading A.grading_inst twists) a).val.obj U)
      (y : ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
        A.gradeAddSubgroupClass A.grading A.grading_inst twists) b).val.obj U),
    (((Sigma.ι
        (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
        (a + b) ≫ integerIso.hom).val.app U).hom
      ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
        A.gradeAddSubgroupClass A.grading A.grading_inst twists).mul U a b x y) :
      (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U) =
      (fun (x y : (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U) ↦ x * y)
        (((Sigma.ι
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
          a ≫ integerIso.hom).val.app U).hom x)
        (((Sigma.ι
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
          b ≫ integerIso.hom).val.app U).hom y)
  /-- The nonnegative direct-sum presentation carries the degree-zero twist unit to the unit
  of the presented algebra. -/
  nonnegative_one : ∀ U : (A.proj.Opens)ᵒᵖ,
    (((Sigma.ι (nonnegativeTwists A twists) 0 ≫ nonnegativeIso.hom).val.app U).hom
      ((nonnegativeTwistAlgebra A twists).one U) :
      (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U) =
      (1 : (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U)
  /-- The nonnegative direct-sum presentation carries homogeneous twist multiplication to
  multiplication in the presented algebra. -/
  nonnegative_mul : ∀ (U : (A.proj.Opens)ᵒᵖ) (a b : ℕ)
      (x : ((nonnegativeTwistAlgebra A twists) a).val.obj U)
      (y : ((nonnegativeTwistAlgebra A twists) b).val.obj U),
    (((Sigma.ι (nonnegativeTwists A twists) (a + b) ≫
        nonnegativeIso.hom).val.app U).hom
      ((nonnegativeTwistAlgebra A twists).mul U a b x y) :
      (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U) =
      (fun (x y : (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U) ↦ x * y)
        (((Sigma.ι (nonnegativeTwists A twists) a ≫
          nonnegativeIso.hom).val.app U).hom x)
        (((Sigma.ι (nonnegativeTwists A twists) b ≫
          nonnegativeIso.hom).val.app U).hom y)
  /-- On every nonnegative summand, the algebra inclusion is the canonical inclusion into the
  integral direct sum. -/
  inclusion_ι : ∀ n : ℕ,
    Sigma.ι (nonnegativeTwists A twists) n ≫ nonnegativeIso.hom ≫
      Scheme.QcAlgebraUnder.underlyingModuleMap A.proj inclusion =
      Sigma.ι
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
          (n : ℤ) ≫ integerIso.hom

namespace TwistTotals

/-- Construct the two total twist algebras from their explicit algebra objects, direct-sum
presentations, and inclusion compatibility. -/
def of (A : Scheme.Hom.AbsoluteProjModel)
    (twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst)
    (integer nonnegative : A.proj.QcAlgebraUnder) (inclusion : nonnegative ⟶ integer)
    (integerIso :
      (GradedObject.Total.functor (I := ℤ) (C := A.proj.Modules)).obj
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject ≅
        Scheme.QcAlgebraUnder.underlyingModule A.proj integer)
    (nonnegativeIso :
      (GradedObject.Total.functor (I := ℕ) (C := A.proj.Modules)).obj
          (nonnegativeTwists A twists) ≅
        Scheme.QcAlgebraUnder.underlyingModule A.proj nonnegative)
    (integer_one : ∀ U : (A.proj.Opens)ᵒᵖ,
      (((Sigma.ι
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
          0 ≫ integerIso.hom).val.app U).hom
        ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists).one U) :
        (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U) =
        (1 : (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U))
    (integer_mul : ∀ (U : (A.proj.Opens)ᵒᵖ) (a b : ℤ)
        (x : ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists) a).val.obj U)
        (y : ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists) b).val.obj U),
      (((Sigma.ι
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
          (a + b) ≫ integerIso.hom).val.app U).hom
        ((@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
          A.gradeAddSubgroupClass A.grading A.grading_inst twists).mul U a b x y) :
        (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U) =
        (fun (x y : (Scheme.QcAlgebraUnder.sheaf A.proj integer).1.obj U) ↦ x * y)
          (((Sigma.ι
            (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
              A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
            a ≫ integerIso.hom).val.app U).hom x)
          (((Sigma.ι
            (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
              A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
            b ≫ integerIso.hom).val.app U).hom y))
    (nonnegative_one : ∀ U : (A.proj.Opens)ᵒᵖ,
      (((Sigma.ι (nonnegativeTwists A twists) 0 ≫ nonnegativeIso.hom).val.app U).hom
        ((nonnegativeTwistAlgebra A twists).one U) :
        (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U) =
        (1 : (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U))
    (nonnegative_mul : ∀ (U : (A.proj.Opens)ᵒᵖ) (a b : ℕ)
        (x : ((nonnegativeTwistAlgebra A twists) a).val.obj U)
        (y : ((nonnegativeTwistAlgebra A twists) b).val.obj U),
      (((Sigma.ι (nonnegativeTwists A twists) (a + b) ≫
          nonnegativeIso.hom).val.app U).hom
        ((nonnegativeTwistAlgebra A twists).mul U a b x y) :
        (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U) =
        (fun (x y : (Scheme.QcAlgebraUnder.sheaf A.proj nonnegative).1.obj U) ↦ x * y)
          (((Sigma.ι (nonnegativeTwists A twists) a ≫
            nonnegativeIso.hom).val.app U).hom x)
          (((Sigma.ι (nonnegativeTwists A twists) b ≫
            nonnegativeIso.hom).val.app U).hom y))
    (inclusion_ι : ∀ n : ℕ,
      Sigma.ι (nonnegativeTwists A twists) n ≫ nonnegativeIso.hom ≫
          Scheme.QcAlgebraUnder.underlyingModuleMap A.proj inclusion =
        Sigma.ι
            (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
              A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
            (n : ℤ) ≫ integerIso.hom) :
    TwistTotals A twists where
  integer := integer
  nonnegative := nonnegative
  inclusion := inclusion
  integerIso := integerIso
  nonnegativeIso := nonnegativeIso
  integer_one := integer_one
  integer_mul := integer_mul
  nonnegative_one := nonnegative_one
  nonnegative_mul := nonnegative_mul
  inclusion_ι := inclusion_ι

/-- The inclusion of total twist algebras agrees with the canonical inclusion on every
nonnegative homogeneous summand. -/
theorem inclusion_ι_apply {A : Scheme.Hom.AbsoluteProjModel}
    {twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst}
    (T : TwistTotals A twists) (n : ℕ) :
    Sigma.ι (nonnegativeTwists A twists) n ≫ T.nonnegativeIso.hom ≫
        Scheme.QcAlgebraUnder.underlyingModuleMap A.proj T.inclusion =
      Sigma.ι
          (@ProjTwistAlgebra.algebra A.ring A.grade A.ring.commRing A.gradeSetLike
            A.gradeAddSubgroupClass A.grading A.grading_inst twists).toGradedObject
          (n : ℤ) ≫ T.integerIso.hom := sorry

end TwistTotals

end AlgebraicGeometry.ProjSpec
