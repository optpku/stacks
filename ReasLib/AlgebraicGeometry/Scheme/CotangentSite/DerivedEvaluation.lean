/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Evaluation
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Fibered.CategoryHomology

/-!
# Standard-resolution computation of derived projection lower shriek

The standard polynomial affine resolution is pointlike in each fibre. Evaluation
computes fibre homology naturally on the Zariski site, and its sheafified complex
represents the total left derived functor of projection lower shriek.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits AlgebraicTopology
open HomologicalComplex FiberedCategoryOver.FiberHomology Functor.LeftDerived
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u w qS qT

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- The standard affine cosimplicial resolution has pointlike mapping spaces in its fibre. -/
theorem standardCosimplicial_hasHomSpaces (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] (U : X.smallZariskiSite) :
    CosimplicialObject.Pointlike.HasHomSpaces (standardCosimplicial Λ X U) := sorry

/-- Standard-resolution evaluation homology agrees with fibre bar homology as a presheaf. -/
theorem evalComplex_homology_isomorphic_fiberHomology_presheaf
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] [UnivLE.{u + 1, w}]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic ((evalComplex Λ X F).homology n)
      (Bar.presheaf (fiberedOver Λ X) F n) := sorry

/-- Evaluation on a standard affine cosimplicial object computes homology in its fibre. -/
theorem evalComplex_homology_isomorphic_fiberHomology
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] [UnivLE.{u + 1, w}]
    (F : (category Λ X)ᵒᵖ ⥤ AddCommGrpCat.{w}) (U : X.smallZariskiSite) (n : ℕ) :
    IsIsomorphic
      (((CosimplicialObject.Evaluation.complex AddCommGrpCat.{w}
        (standardCosimplicialObj Λ X U)).obj F).homology n)
      (Bar.homology (fiberedOver Λ X) F U n) := sorry

/-- Sheafified evaluation homology computes the projective left derived projection lower shriek. -/
theorem evalSheaf_homology_isomorphic_lowerShriek
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasProjectiveResolutions (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic
      ((presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{w}).obj
        ((evalComplex Λ X F.obj).homology n))
      (((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          X.smallZariskiTopology).leftDerived n |>.obj F) :=
  sorry

/-- The sheafified standard-resolution complex represents total derived projection lower shriek. -/
theorem evalSheafComplex_computes
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasDerivedCategory.{qS} (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    [HasDerivedCategory.{qT} (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
        X.smallZariskiTopology).Additive]
    [(Functor.Homotopy.toDerived
        ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          X.smallZariskiTopology)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{w})
        (ComplexShape.up ℤ))]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) :
    IsIsomorphic (DerivedCategory.Q.obj (evalSheafComplex Λ X F))
      ((Homotopy.functor
          ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
            X.smallZariskiTopology)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F)) :=
  sorry

/-- Sheafified evaluation homology is degree `-n` homology of total derived projection lower shriek. -/
theorem evalSheaf_homology_isomorphic_derivedLowerShriek
    (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{w}]
    [HasZeroObject (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [HasSheafify (topology Λ X) AddCommGrpCat.{w}]
    [((forgetZariski Λ X).sheafPushforwardContinuous AddCommGrpCat.{w}
        (topology Λ X) X.smallZariskiTopology).IsRightAdjoint]
    [HasDerivedCategory.{qS} (Sheaf (topology Λ X) AddCommGrpCat.{w})]
    [HasDerivedCategory.{qT} (Sheaf X.smallZariskiTopology AddCommGrpCat.{w})]
    [((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
        X.smallZariskiTopology).Additive]
    [(Functor.Homotopy.toDerived
        ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
          X.smallZariskiTopology)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (topology Λ X) AddCommGrpCat.{w})
        (ComplexShape.up ℤ))]
    (F : Sheaf (topology Λ X) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic
      ((presheafToSheaf X.smallZariskiTopology AddCommGrpCat.{w}).obj
        ((evalComplex Λ X F.obj).homology n))
      ((DerivedCategory.homologyFunctor
          (Sheaf X.smallZariskiTopology AddCommGrpCat.{w}) (-(n : ℤ))).obj
        ((Homotopy.functor
          ((forgetZariski Λ X).sheafPullback AddCommGrpCat.{w} (topology Λ X)
            X.smallZariskiTopology)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (topology Λ X) AddCommGrpCat.{w}) (0 : ℤ)).obj F))) :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
