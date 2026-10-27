/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.StandardResolution
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Sheafification
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Evaluation on standard polynomial resolutions

Evaluation of a coefficient presheaf on the functorial standard polynomial resolution
gives a chain complex of presheaves. Degreewise sheafification and extension to integer
degrees give a cochain complex supported in nonpositive degrees.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits
open AlgebraicTopology HomologicalComplex
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u vA uA

namespace AlgebraicGeometry.Scheme.CotangentSite

variable {A : Type uA} [Category.{vA} A]

/-- The presheaf obtained by evaluating coefficients on the degree-`n` standard affine object. -/
def evalPresheaf (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ A) (n : ℕ) : X.smallZariskiSiteᵒᵖ ⥤ A :=
  (standardFunctor Λ X ⋙ (CategoryTheory.evaluation SimplexCategory (category Λ X)).obj ⦋n⦌).op ⋙ F

/-- Evaluation at an open recovers the coefficient object of its standard affine term. -/
theorem evalPresheaf_obj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ A) (n : ℕ) (U : X.smallZariskiSite) :
    (evalPresheaf Λ X F n).obj (op U) = F.obj (op (standardAffine Λ X ⦋n⦌ U)) := rfl

variable [Abelian A]

/-- The alternating-face complex of presheaves obtained from the standard polynomial resolution. -/
def evalComplex (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ A) : ChainComplex (X.smallZariskiSiteᵒᵖ ⥤ A) ℕ :=
  (alternatingFaceMapComplex (X.smallZariskiSiteᵒᵖ ⥤ A)).obj
    ((standardFunctor Λ X).op ⋙ (cosimplicialSimplicialEquiv (category Λ X)).functor ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (category Λ X)ᵒᵖ A).obj F).flip

/-- The degree-`n` presheaf of the evaluation complex is degreewise standard affine evaluation. -/
theorem evalComplex_X (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    (F : (category Λ X)ᵒᵖ ⥤ A) (n : ℕ) :
    (evalComplex Λ X F).X n = evalPresheaf Λ X F n := sorry

/-- Degreewise sheafification of the standard-resolution evaluation chain complex. -/
def evalSheafChain (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology A] (F : Sheaf (topology Λ X) A) :
    ChainComplex (Sheaf X.smallZariskiTopology A) ℕ :=
  ((presheafToSheaf X.smallZariskiTopology A).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (evalComplex Λ X F.obj)

/-- The sheafified evaluation complex placed in nonpositive cohomological degrees. -/
def evalSheafComplex (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology A]
    [HasZeroObject (Sheaf X.smallZariskiTopology A)] (F : Sheaf (topology Λ X) A) :
    CochainComplex (Sheaf X.smallZariskiTopology A) ℤ :=
  (evalSheafChain Λ X F).extend ComplexShape.embeddingDownNat

/-- The degree `-n` term is the associated sheaf of degree-`n` standard affine evaluation. -/
theorem evalSheafComplex_X (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]
    [HasSheafify X.smallZariskiTopology A]
    [HasZeroObject (Sheaf X.smallZariskiTopology A)]
    (F : Sheaf (topology Λ X) A) (n : ℕ) :
    (evalSheafComplex Λ X F).X (-(n : ℤ)) =
      (presheafToSheaf X.smallZariskiTopology A).obj (evalPresheaf Λ X F.obj n) := sorry

end AlgebraicGeometry.Scheme.CotangentSite
