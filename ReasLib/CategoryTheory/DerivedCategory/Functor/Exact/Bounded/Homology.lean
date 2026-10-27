/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import Mathlib.CategoryTheory.CatCommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of bounded exact derived functors

Exact functors on bounded-below, bounded-above, and bounded derived categories
commute naturally with homology.  The comparison components are inherited
directly from the ambient derived category, so downstream code need not pass
through the full-subcategory inclusions or manage associators.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

namespace Plus

/-- The objectwise homology comparison for an exact functor on the
bounded-below derived category. -/
@[stacks 015F "bounded-below exact derived functors commute with homology"]
noncomputable abbrev homologyIso (F : A ⥤ₑ B)
    (X : DerivedCategory.Plus A) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B q).obj ((functor F).obj X) ≅
      F.obj.obj ((DerivedCategory.Plus.homologyFunctor A q).obj X) :=
  F.homologyIso X.obj q

/-- Forward naturality of the bounded-below exact-functor homology
comparison. -/
@[reassoc]
theorem homologyIso_hom_naturality (F : A ⥤ₑ B)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) (q : ℤ) :
    (functor F ⋙ DerivedCategory.Plus.homologyFunctor B q).map f ≫
        (homologyIso F Y q).hom =
      (homologyIso F X q).hom ≫
        (DerivedCategory.Plus.homologyFunctor A q ⋙ F.obj).map f := by
  exact (F.homologyFunctorIso q).hom.naturality f.hom

/-- Inverse naturality of the bounded-below exact-functor homology
comparison. -/
@[reassoc]
theorem homologyIso_inv_naturality (F : A ⥤ₑ B)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor A q ⋙ F.obj).map f ≫
        (homologyIso F Y q).inv =
      (homologyIso F X q).inv ≫
        (functor F ⋙ DerivedCategory.Plus.homologyFunctor B q).map f := by
  exact (F.homologyFunctorIso q).inv.naturality f.hom

/-- An exact functor on bounded-below derived categories commutes naturally
with every homology functor. -/
@[stacks 015F "natural bounded-below exact derived homology comparison"]
noncomputable def homologyFunctorIso (F : A ⥤ₑ B) (q : ℤ) :
    functor F ⋙ DerivedCategory.Plus.homologyFunctor B q ≅
      DerivedCategory.Plus.homologyFunctor A q ⋙ F.obj :=
  (CatCommSq.vComp' ⟨compιIso F⟩ ⟨F.homologyFunctorIso q⟩).iso

namespace homologyFunctorIso

/-- The components of the bounded-below homology comparison are the ambient
exact-functor homology comparisons. -/
@[simp]
theorem app (F : A ⥤ₑ B) (X : DerivedCategory.Plus A) (q : ℤ) :
    (homologyFunctorIso F q).app X = homologyIso F X q := by
  apply Iso.ext
  simp only [homologyFunctorIso, Iso.app_hom, CatCommSq.vComp_iso_hom_app,
    compιIso, ObjectProperty.FullSubcategory.restrict.compιIso,
    ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
    homologyIso, ExactFunctor.homologyIso, Iso.app_hom]
  change (DerivedCategory.homologyFunctor B q).map (𝟙 (F.mapDerivedCategory.obj X.obj)) ≫
    (F.homologyIso X.obj q).hom = (F.homologyIso X.obj q).hom
  rw [Functor.map_id, Category.id_comp]

end homologyFunctorIso

end Plus

namespace Minus

/-- The objectwise homology comparison for an exact functor on the
bounded-above derived category. -/
@[stacks 015F "bounded-above exact derived functors commute with homology"]
noncomputable abbrev homologyIso (F : A ⥤ₑ B)
    (X : DerivedCategory.Minus A) (q : ℤ) :
    (DerivedCategory.Minus.homologyFunctor B q).obj ((functor F).obj X) ≅
      F.obj.obj ((DerivedCategory.Minus.homologyFunctor A q).obj X) :=
  F.homologyIso X.obj q

/-- Forward naturality of the bounded-above exact-functor homology
comparison. -/
@[reassoc]
theorem homologyIso_hom_naturality (F : A ⥤ₑ B)
    {X Y : DerivedCategory.Minus A} (f : X ⟶ Y) (q : ℤ) :
    (functor F ⋙ DerivedCategory.Minus.homologyFunctor B q).map f ≫
        (homologyIso F Y q).hom =
      (homologyIso F X q).hom ≫
        (DerivedCategory.Minus.homologyFunctor A q ⋙ F.obj).map f := by
  exact (F.homologyFunctorIso q).hom.naturality f.hom

/-- Inverse naturality of the bounded-above exact-functor homology
comparison. -/
@[reassoc]
theorem homologyIso_inv_naturality (F : A ⥤ₑ B)
    {X Y : DerivedCategory.Minus A} (f : X ⟶ Y) (q : ℤ) :
    (DerivedCategory.Minus.homologyFunctor A q ⋙ F.obj).map f ≫
        (homologyIso F Y q).inv =
      (homologyIso F X q).inv ≫
        (functor F ⋙ DerivedCategory.Minus.homologyFunctor B q).map f := by
  exact (F.homologyFunctorIso q).inv.naturality f.hom

/-- An exact functor on bounded-above derived categories commutes naturally
with every homology functor. -/
@[stacks 015F "natural bounded-above exact derived homology comparison"]
noncomputable def homologyFunctorIso (F : A ⥤ₑ B) (q : ℤ) :
    functor F ⋙ DerivedCategory.Minus.homologyFunctor B q ≅
      DerivedCategory.Minus.homologyFunctor A q ⋙ F.obj :=
  (CatCommSq.vComp' ⟨compιIso F⟩ ⟨F.homologyFunctorIso q⟩).iso

namespace homologyFunctorIso

/-- The components of the bounded-above homology comparison are the ambient
exact-functor homology comparisons. -/
@[simp]
theorem app (F : A ⥤ₑ B) (X : DerivedCategory.Minus A) (q : ℤ) :
    (homologyFunctorIso F q).app X = homologyIso F X q := by
  apply Iso.ext
  simp only [homologyFunctorIso, Iso.app_hom, CatCommSq.vComp_iso_hom_app,
    compιIso, ObjectProperty.FullSubcategory.restrict.compιIso,
    ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
    homologyIso, ExactFunctor.homologyIso, Iso.app_hom]
  change (DerivedCategory.homologyFunctor B q).map (𝟙 (F.mapDerivedCategory.obj X.obj)) ≫
    (F.homologyIso X.obj q).hom = (F.homologyIso X.obj q).hom
  rw [Functor.map_id, Category.id_comp]

end homologyFunctorIso

end Minus

namespace Bounded

/-- The objectwise homology comparison for an exact functor on the bounded
derived category. -/
@[stacks 015F "bounded exact derived functors commute with homology"]
noncomputable abbrev homologyIso (F : A ⥤ₑ B)
    (X : DerivedCategory.Bounded A) (q : ℤ) :
    (DerivedCategory.Bounded.homologyFunctor B q).obj ((functor F).obj X) ≅
      F.obj.obj ((DerivedCategory.Bounded.homologyFunctor A q).obj X) :=
  F.homologyIso X.obj q

/-- Forward naturality of the bounded exact-functor homology comparison. -/
@[reassoc]
theorem homologyIso_hom_naturality (F : A ⥤ₑ B)
    {X Y : DerivedCategory.Bounded A} (f : X ⟶ Y) (q : ℤ) :
    (functor F ⋙ DerivedCategory.Bounded.homologyFunctor B q).map f ≫
        (homologyIso F Y q).hom =
      (homologyIso F X q).hom ≫
        (DerivedCategory.Bounded.homologyFunctor A q ⋙ F.obj).map f := by
  exact (F.homologyFunctorIso q).hom.naturality f.hom

/-- Inverse naturality of the bounded exact-functor homology comparison. -/
@[reassoc]
theorem homologyIso_inv_naturality (F : A ⥤ₑ B)
    {X Y : DerivedCategory.Bounded A} (f : X ⟶ Y) (q : ℤ) :
    (DerivedCategory.Bounded.homologyFunctor A q ⋙ F.obj).map f ≫
        (homologyIso F Y q).inv =
      (homologyIso F X q).inv ≫
        (functor F ⋙ DerivedCategory.Bounded.homologyFunctor B q).map f := by
  exact (F.homologyFunctorIso q).inv.naturality f.hom

/-- An exact functor on bounded derived categories commutes naturally with
every homology functor. -/
@[stacks 015F "natural bounded exact derived homology comparison"]
noncomputable def homologyFunctorIso (F : A ⥤ₑ B) (q : ℤ) :
    functor F ⋙ DerivedCategory.Bounded.homologyFunctor B q ≅
      DerivedCategory.Bounded.homologyFunctor A q ⋙ F.obj :=
  (CatCommSq.vComp' ⟨compιIso F⟩ ⟨F.homologyFunctorIso q⟩).iso

namespace homologyFunctorIso

/-- The components of the bounded homology comparison are the ambient
exact-functor homology comparisons. -/
@[simp]
theorem app (F : A ⥤ₑ B) (X : DerivedCategory.Bounded A) (q : ℤ) :
    (homologyFunctorIso F q).app X = homologyIso F X q := by
  apply Iso.ext
  simp only [homologyFunctorIso, Iso.app_hom, CatCommSq.vComp_iso_hom_app,
    compιIso, ObjectProperty.FullSubcategory.restrict.compιIso,
    ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app,
    homologyIso, ExactFunctor.homologyIso, Iso.app_hom]
  change (DerivedCategory.homologyFunctor B q).map (𝟙 (F.mapDerivedCategory.obj X.obj)) ≫
    (F.homologyIso X.obj q).hom = (F.homologyIso X.obj q).hom
  rw [Functor.map_id, Category.id_comp]

end homologyFunctorIso

end Bounded

end CategoryTheory.ExactFunctor.Derived
