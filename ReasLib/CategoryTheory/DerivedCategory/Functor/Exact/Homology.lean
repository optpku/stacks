/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Homology of exact functors on derived categories

@stack 015F

An exact additive functor commutes naturally with every derived-category homology functor. The
primary API is a natural isomorphism; its objectwise component and the reverse-direction
compatibility entry are provided for calculations and existing downstream users.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The source of the exact-functor homology comparison is a localization
lift of homology after applying the functor to cochain complexes. -/
noncomputable def homologySourceFactors (q : ℤ) :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙
        (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryFactors
      (DerivedCategory.homologyFunctor B q) ≪≫
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.homologyFunctorFactors B q)

/-- The target of the exact-functor homology comparison is a localization
lift of applying the functor after cochain-complex homology. -/
noncomputable def homologyTargetFactors (q : ℤ) :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙
        (DerivedCategory.homologyFunctor A q ⋙ F) ≅
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedCategory.homologyFunctorFactors A q) F

/-- The source derived homology functor carries its canonical localization
lifting structure. -/
noncomputable instance homologySourceLifting (q : ℤ) :
    Localization.Lifting
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q) :=
  ⟨homologySourceFactors F q⟩

/-- The target derived homology functor carries its canonical localization
lifting structure. -/
noncomputable instance homologyTargetLifting (q : ℤ) :
    Localization.Lifting
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F)
      (DerivedCategory.homologyFunctor A q ⋙ F) :=
  ⟨homologyTargetFactors F q⟩

/-- An exact functor commutes naturally with degree-`q` homology after passage to derived categories. -/
noncomputable def homologyFunctorIso (q : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q ≅
      DerivedCategory.homologyFunctor A q ⋙ F :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q)
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q)
    (DerivedCategory.homologyFunctor A q ⋙ F)
    (HomologicalComplex.mapHomologyFunctorIso F q)

/-- The objectwise exact-functor homology comparison is the component of
the canonical natural comparison. -/
noncomputable abbrev homologyIso (K : DerivedCategory A) (q : ℤ) :
    (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor A q).obj K) :=
  (homologyFunctorIso F q).app K

/-- The forward exact-functor homology comparisons are natural in the
derived object. -/
@[reassoc]
theorem homologyIso_hom_naturality
    {K L : DerivedCategory A} (f : K ⟶ L) (q : ℤ) :
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q).map f ≫
        (homologyIso F L q).hom =
      (homologyIso F K q).hom ≫
        (DerivedCategory.homologyFunctor A q ⋙ F).map f := sorry

/-- The inverse exact-functor homology comparisons are natural in the derived object. -/
@[reassoc]
theorem homologyIso_inv_naturality {K L : DerivedCategory A} (f : K ⟶ L) (q : ℤ) :
    (DerivedCategory.homologyFunctor A q ⋙ F).map f ≫
        (homologyIso F L q).inv =
      (homologyIso F K q).inv ≫
        (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q).map f := sorry

/-- Computation of the forward exact-functor homology comparison on a
cochain complex viewed in the derived category. -/
theorem homologyFunctorIso_hom_app_Q (K : CochainComplex A ℤ) (q : ℤ) :
    (homologyFunctorIso F q).hom.app (DerivedCategory.Q.obj K) =
      (homologySourceFactors F q).hom.app K ≫
        (HomologicalComplex.mapHomologyFunctorIso F q).hom.app K ≫
        (homologyTargetFactors F q).inv.app K := sorry

/-- Computation of the inverse exact-functor homology comparison on a
cochain complex viewed in the derived category. -/
theorem homologyFunctorIso_inv_app_Q (K : CochainComplex A ℤ) (q : ℤ) :
    (homologyFunctorIso F q).inv.app (DerivedCategory.Q.obj K) =
      (homologyTargetFactors F q).hom.app K ≫
        (HomologicalComplex.mapHomologyFunctorIso F q).inv.app K ≫
        (homologySourceFactors F q).inv.app K := sorry

namespace homologyFunctorIso

/-- The component of the natural exact-functor homology comparison is `homologyIso`. -/
@[simp]
theorem app (K : DerivedCategory A) (q : ℤ) :
    (homologyFunctorIso F q).app K = homologyIso F K q := sorry

end homologyFunctorIso

end CategoryTheory.Functor.MapDerivedCategory

namespace CategoryTheory.ExactFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable (F : A ⥤ₑ B)

/-- A bundled exact functor commutes naturally with every derived-category
homology functor. -/
noncomputable abbrev homologyFunctorIso (q : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q ≅
      DerivedCategory.homologyFunctor A q ⋙ F.obj :=
  Functor.MapDerivedCategory.homologyFunctorIso F.obj q

/-- The objectwise component of the bundled exact-functor homology
comparison. -/
noncomputable abbrev homologyIso (K : DerivedCategory A) (q : ℤ) :
    (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj K) ≅
      F.obj.obj ((DerivedCategory.homologyFunctor A q).obj K) :=
  (F.homologyFunctorIso q).app K

/-- Forward naturality of the bundled exact-functor homology comparison. -/
@[reassoc]
theorem homologyIso_hom_naturality
    {K L : DerivedCategory A} (f : K ⟶ L) (q : ℤ) :
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q).map f ≫
        (F.homologyIso L q).hom =
      (F.homologyIso K q).hom ≫
        (DerivedCategory.homologyFunctor A q ⋙ F.obj).map f := sorry

/-- Inverse naturality of the bundled exact-functor homology comparison. -/
@[reassoc]
theorem homologyIso_inv_naturality
    {K L : DerivedCategory A} (f : K ⟶ L) (q : ℤ) :
    (DerivedCategory.homologyFunctor A q ⋙ F.obj).map f ≫
        (F.homologyIso L q).inv =
      (F.homologyIso K q).inv ≫
        (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q).map f := sorry

namespace homologyFunctorIso

/-- The components of the bundled homology comparison are
`ExactFunctor.homologyIso`. -/
@[simp]
theorem app (K : DerivedCategory A) (q : ℤ) :
    (F.homologyFunctorIso q).app K = F.homologyIso K q := sorry

end homologyFunctorIso

end CategoryTheory.ExactFunctor

namespace CategoryTheory

/-- Compatibility entry for the reverse-direction component of the natural exact-functor
homology comparison. New functorial code should use
`Functor.MapDerivedCategory.homologyFunctorIso`. -/
noncomputable abbrev exactFunctor_homology_iso_mapDerivedCategory
    {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A) (q : ℤ) :
    F.obj ((DerivedCategory.homologyFunctor A q).obj K) ≅
      (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj K) :=
  (Functor.MapDerivedCategory.homologyFunctorIso F q).symm.app K

end CategoryTheory
