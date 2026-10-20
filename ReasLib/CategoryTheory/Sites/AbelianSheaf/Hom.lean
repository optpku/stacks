/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Internal Hom of abelian sheaves
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
/-- The additive restriction map on presheaf Hom over slices. -/
def abelianSheafHom_restrict (A B : Sheaf J AddCommGrpCat.{max w u v})
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) →+
      ((CategoryTheory.Over.forget Y.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget Y.unop).op ⋙ B.obj) where
  toFun α := Functor.whiskerLeft (CategoryTheory.Over.map f.unop).op α
  map_zero' := ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Over.map f.unop).op).map_zero _ _
  map_add' := fun _ _ ↦ ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Over.map f.unop).op).map_add

/-- Restriction along an identity acts identically on local morphisms. -/
private theorem abelianSheafHomPresheaf_map_id
    (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    AddCommGrpCat.ofHom (abelianSheafHom_restrict J A B (𝟙 X)) =
      𝟙 (AddCommGrpCat.of
        ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶
          (CategoryTheory.Over.forget X.unop).op ⋙ B.obj)) :=
  sorry

/-- Restriction of local morphisms respects composition. -/
private theorem abelianSheafHomPresheaf_map_comp
    (A B : Sheaf J AddCommGrpCat.{max w u v}) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    AddCommGrpCat.ofHom (abelianSheafHom_restrict J A B (f ≫ g)) =
      AddCommGrpCat.ofHom (abelianSheafHom_restrict J A B f) ≫
        AddCommGrpCat.ofHom (abelianSheafHom_restrict J A B g) :=
  sorry

/-- The presheaf of abelian groups of local morphisms between abelian sheaves. -/
def abelianSheafHomPresheaf (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max w u v} where
  obj X :=
    AddCommGrpCat.of
      ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj)
  map f := AddCommGrpCat.ofHom (abelianSheafHom_restrict J A B f)
  map_id X := by exact abelianSheafHomPresheaf_map_id J A B X
  map_comp f g := by exact abelianSheafHomPresheaf_map_comp J A B f g

/-- The local-Hom presheaf of abelian sheaves satisfies the sheaf condition. -/
theorem abelianSheafHomPresheaf_isSheaf (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    Presheaf.IsSheaf J (abelianSheafHomPresheaf J A B) :=
  sorry

/-- Internal Hom of abelian sheaves: the sheaf `Hom(A, B)` whose sections over `X`
are morphisms of restrictions to `C/X`. -/
def abelianSheafHom (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    Sheaf J AddCommGrpCat.{max w u v} :=
  ⟨abelianSheafHomPresheaf J A B, abelianSheafHomPresheaf_isSheaf J A B⟩

/-- Sections of `abelianSheafHom A B` at `X` are morphisms of restrictions to `C/X`. -/
theorem abelianSheafHom_obj (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    (abelianSheafHom J A B).obj.obj X =
      AddCommGrpCat.of
        ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) :=
  rfl

variable [J.HasSheafCompose (forget AddCommGrpCat.{max w u v})]

/-- Componentwise equivalence between raw local Hom groups of `abelianSheafHom`
and sheaf morphisms on the over-site, which are the sections of `sheafHom`. -/
def abelianSheafHom_forget_equiv (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    ((sheafForget J).obj (abelianSheafHom J A B)).obj.obj X ≃
      (sheafHom A B).obj.obj X :=
  ((sheafHom'Iso A B).symm.app X).toEquiv

/-- Forgetting the abelian group structure on `abelianSheafHom A B` is canonically
isomorphic to the type-valued internal Hom sheaf. -/
def abelianSheafHom_forget (A B : Sheaf J AddCommGrpCat.{max w u v}) :
    (sheafForget J).obj (abelianSheafHom J A B) ≅ sheafHom A B :=
  (fullyFaithfulSheafToPresheaf J (Type (max w u v))).preimageIso (sheafHom'Iso A B).symm

/-- The component of `abelianSheafHom_forget` at `X` is `abelianSheafHom_forget_equiv`. -/
theorem abelianSheafHom_forget_hom_app
    (A B : Sheaf J AddCommGrpCat.{max w u v}) (X : Cᵒᵖ) :
    (abelianSheafHom_forget J A B).hom.hom.app X =
      (Equiv.toIso (abelianSheafHom_forget_equiv J A B X)).hom :=
  sorry

/-- The additive precomposition map on local Hom groups. -/
def abelianSheafHom_precomp
    (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) (X : Cᵒᵖ) :
    ((CategoryTheory.Over.forget X.unop).op ⋙ A.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) →+
      ((CategoryTheory.Over.forget X.unop).op ⋙ A'.obj ⟶ (CategoryTheory.Over.forget X.unop).op ⋙ B.obj) where
  toFun φ := Functor.whiskerLeft (CategoryTheory.Over.forget X.unop).op f.hom ≫ φ
  map_zero' := Limits.comp_zero
  map_add' := fun _ _ ↦ Preadditive.comp_add _ _ _ _ _ _

/-- Naturality of precomposition against restriction. -/
private theorem abelianSheafHom_map_naturality
    (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    (abelianSheafHom J A B).obj.map g ≫
        AddCommGrpCat.ofHom (abelianSheafHom_precomp J A A' B f Y) =
      AddCommGrpCat.ofHom (abelianSheafHom_precomp J A A' B f X) ≫
        (abelianSheafHom J A' B).obj.map g :=
  sorry

/-- Precomposition `Hom(A, B) ⟶ Hom(A', B)` induced by `f : A' ⟶ A`. -/
def abelianSheafHom_map (A A' B : Sheaf J AddCommGrpCat.{max w u v}) (f : A' ⟶ A) :
    abelianSheafHom J A B ⟶ abelianSheafHom J A' B where
  hom :=
    { app := fun X ↦ AddCommGrpCat.ofHom (abelianSheafHom_precomp J A A' B f X)
      naturality := by intro _ _ g; exact abelianSheafHom_map_naturality J A A' B f g }

/-- `abelianSheafHom_map` of a zero morphism is zero. -/
theorem abelianSheafHom_map_zero (A A' B : Sheaf J AddCommGrpCat.{max w u v}) :
    abelianSheafHom_map J A A' B (0 : A' ⟶ A) = 0 :=
  sorry

/-- `abelianSheafHom_map` reverses composition. -/
theorem abelianSheafHom_map_comp (A A' A'' B : Sheaf J AddCommGrpCat.{max w u v})
    (f : A'' ⟶ A') (g : A' ⟶ A) :
    abelianSheafHom_map J A A'' B (f ≫ g) =
      abelianSheafHom_map J A A' B g ≫ abelianSheafHom_map J A' A'' B f :=
  sorry

end CategoryTheory
