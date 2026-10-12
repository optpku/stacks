/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of exact functors on derived categories

@stack 015F

This leaf constructs the composition comparison from localization
factorizations.  The comparison is therefore natural by construction and
does not choose representatives of derived-category objects.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-- The canonical factorization showing that the composite of the derived
functors of `F` and `G` lifts the cochain functor of `F.comp G`. -/
@[stacks 015F "factorization for composites of exact derived functors"]
noncomputable def compFactors (F : A ⥤ₑ B) (G : B ⥤ₑ C) :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙
        (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ≅
      (F.comp G).obj.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.obj.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (F.obj.mapHomologicalComplex (up ℤ))
          G.obj.mapDerivedCategoryFactors ≪≫
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (Functor.mapHomologicalComplexCompIso
                (Iso.refl (F.obj ⋙ G.obj)) (up ℤ))
              (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)

/-- The composite of the derived functors of `F` and `G` is canonically a
localization lift of the cochain functor of `F.comp G`. -/
noncomputable instance compLifting (F : A ⥤ₑ B) (G : B ⥤ₑ C) :
    Localization.Lifting
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
      (HomologicalComplex.quasiIso A (up ℤ))
      ((F.comp G).obj.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C))
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
  ⟨compFactors F G⟩

/-- Passage to derived categories commutes naturally with composition of
bundled exact functors. -/
@[stacks 015F "passage to derived categories preserves exact-functor composition"]
noncomputable def compFunctorIso (F : A ⥤ₑ B) (G : B ⥤ₑ C) :
    (F.comp G).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (up ℤ))
    ((F.comp G).obj.mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C))
    ((F.comp G).obj.mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C))
    (F.comp G).mapDerivedCategory
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (Iso.refl _)

/-- The derived-category value of a composite of exact functors is
canonically isomorphic to the iterated derived-category value. -/
@[stacks 015F "objectwise exact-derived composition comparison"]
noncomputable abbrev compObjIso (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (K : DerivedCategory A) :
    (F.comp G).mapDerivedCategory.obj K ≅
      G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) :=
  (compFunctorIso F G).app K

/-- Computation of the forward composition comparison on an object in the
image of the localization functor. -/
theorem compFunctorIso_hom_app_Q
    (F : A ⥤ₑ B) (G : B ⥤ₑ C) (K : CochainComplex A ℤ) :
    (compFunctorIso F G).hom.app (DerivedCategory.Q.obj K) =
      (F.comp G).obj.mapDerivedCategoryFactors.hom.app K ≫
        (compFactors F G).inv.app K := sorry

/-- Computation of the inverse composition comparison on an object in the
image of the localization functor. -/
theorem compFunctorIso_inv_app_Q
    (F : A ⥤ₑ B) (G : B ⥤ₑ C) (K : CochainComplex A ℤ) :
    (compFunctorIso F G).inv.app (DerivedCategory.Q.obj K) =
      (compFactors F G).hom.app K ≫
        (F.comp G).obj.mapDerivedCategoryFactors.inv.app K := sorry

/-- Forward naturality of the comparison between passage to the derived
category and composition of bundled exact functors. -/
@[reassoc]
theorem compObjIso_hom_naturality
    (F : A ⥤ₑ B) (G : B ⥤ₑ C) {K L : DerivedCategory A} (f : K ⟶ L) :
    (F.comp G).mapDerivedCategory.map f ≫ (compObjIso F G L).hom =
      (compObjIso F G K).hom ≫
        (F.mapDerivedCategory ⋙ G.mapDerivedCategory).map f := sorry

/-- Inverse naturality of the comparison between passage to the derived
category and composition of bundled exact functors. -/
@[reassoc]
theorem compObjIso_inv_naturality
    (F : A ⥤ₑ B) (G : B ⥤ₑ C) {K L : DerivedCategory A} (f : K ⟶ L) :
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory).map f ≫
        (compObjIso F G L).inv =
      (compObjIso F G K).inv ≫
        (F.comp G).mapDerivedCategory.map f := sorry

namespace compFunctorIso

/-- The components of `compFunctorIso` are the objectwise composition
comparisons. -/
@[simp]
theorem app (F : A ⥤ₑ B) (G : B ⥤ₑ C) (K : DerivedCategory A) :
    (compFunctorIso F G).app K = compObjIso F G K := sorry

end compFunctorIso

end CategoryTheory.ExactFunctor.MapDerivedCategory

namespace CategoryTheory.Functor.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-- Compatibility name for the composition comparison of bundled exact
functors.  New code should use
`ExactFunctor.MapDerivedCategory.compFunctorIso`. -/
@[deprecated ExactFunctor.MapDerivedCategory.compFunctorIso (since := "2026-08-03")]
noncomputable abbrev compFunctorIso (F : A ⥤ₑ B) (G : B ⥤ₑ C) :
    (F.comp G).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  ExactFunctor.MapDerivedCategory.compFunctorIso F G

/-- Compatibility name for the objectwise composition comparison of
bundled exact functors.  New code should use
`ExactFunctor.MapDerivedCategory.compObjIso`. -/
@[deprecated ExactFunctor.MapDerivedCategory.compObjIso (since := "2026-08-03")]
noncomputable abbrev compObjIso (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (K : DerivedCategory A) :
    (F.comp G).mapDerivedCategory.obj K ≅
      G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) :=
  ExactFunctor.MapDerivedCategory.compObjIso F G K

/-- Compatibility alias for computation of the forward composition
comparison.  New code should use
`ExactFunctor.MapDerivedCategory.compFunctorIso_hom_app_Q`. -/
@[deprecated (since := "2026-08-03")]
alias compFunctorIso_hom_app_Q :=
  ExactFunctor.MapDerivedCategory.compFunctorIso_hom_app_Q

end CategoryTheory.Functor.MapDerivedCategory
