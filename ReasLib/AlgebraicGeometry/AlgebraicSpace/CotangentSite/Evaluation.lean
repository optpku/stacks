/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.CosimplicialEvaluation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.StandardResolution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Sheafification
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Fibered.CategoryHomology
public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.LeftDerived
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Homology of standard affine evaluation

Evaluation on standard affine resolutions computes homology in the projection fibers.
Degreewise sheafification computes the total left-derived projection lower shriek.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u w q

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{w}]
variable [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
variable [((forget Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
    (topology Λ X) (smallEtaleTopology X)).IsRightAdjoint]

/-- Standard affine evaluation computes homology of a sheaf on the projection fiber. -/
theorem eval_homology_iso [UnivLE.{u + 1, w}]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w})
    (U : smallEtaleSite X) (n : ℕ) :
    IsIsomorphic
      (((CosimplicialObject.Evaluation.complex AddCommGrpCat.{w}
          ((standardAffine Λ X).obj U)).obj F.obj).homology n)
      (FiberedCategoryOver.FiberHomology.Bar.homology
        (FiberedCategoryOver.ofFunctor (forget Λ X)) F.obj U n) :=
  sorry

/-- Sheafification of standard affine evaluation homology computes the projective
left-derived projection lower shriek. -/
theorem sheafify_iso_lowerShriek
    [UnivLE.{u + 1, w}]
    [HasProjectiveResolutions (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic
      ((presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{w}).obj
        ((CosimplicialObject.Evaluation.Family.presheafComplex
          (standardAffine Λ X) F.obj).homology n))
      (((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          (smallEtaleTopology X)).leftDerived n |>.obj F) :=
  sorry

variable [HasDerivedCategory.{q} (Sheaf (topology Λ X) AddCommGrpCat.{w})]
variable [HasDerivedCategory.{q} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w})]
variable [((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
    (smallEtaleTopology X)).Additive]
variable [(Functor.Homotopy.toDerived
    ((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
      (smallEtaleTopology X))).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{w})
    (ComplexShape.up ℤ))]

/-- The sheafified standard affine evaluation complex represents total left-derived
projection lower shriek of a sheaf placed in degree zero. -/
theorem evalSheafComplex_iso [UnivLE.{u + 1, w}]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CosimplicialObject.Evaluation.Family.sheafComplex
        (standardAffine Λ X) F.obj (smallEtaleTopology X)))
      ((Functor.LeftDerived.Homotopy.functor
          ((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
            (smallEtaleTopology X))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F)) :=
  sorry

/-- Sheafified degree-`n` evaluation homology is degree-`-n` homology of total left-derived
projection lower shriek of a sheaf placed in degree zero. -/
theorem evalSheafComplex_homology_iso
    [UnivLE.{u + 1, w}]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic
      ((presheafToSheaf (smallEtaleTopology X) AddCommGrpCat.{w}).obj
        ((CosimplicialObject.Evaluation.Family.presheafComplex
          (standardAffine Λ X) F.obj).homology n))
      ((DerivedCategory.homologyFunctor
          (Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}) (-(n : ℤ))).obj
        ((Functor.LeftDerived.Homotopy.functor
            ((forget Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
              (smallEtaleTopology X))).obj
          ((DerivedCategory.singleFunctor
              (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
