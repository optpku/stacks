/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProperSupport

/-!
# Direct image with compact support on the small étale site

The underived abelian functor `f_!` along a separated, locally finite-type
morphism, realized as the subsheaf of `f_*` of sections whose support is proper
over the base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable [LocallyOfFiniteType f]

/-- The additive subgroup of sections of `F` on `X_V` whose support is proper
over `V`. These are the sections of `f_! F` over `V`. -/
abbrev compactSupportSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    AddSubgroup (F.obj.obj (op ((smallEtalePullback f).obj V))) :=
  properSupportSections f F V

variable [IsSeparated f]

/-- Restriction along an étale morphism of the base preserves proper support of
sections. -/
theorem restrict_mem_compactSupportSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V W : Y.Etale}
    (g : W ⟶ V) (σ : compactSupportSections f F V) :
    (F.obj.map ((smallEtalePullback f).map g).op)
        ((compactSupportSections f F V).subtype σ) ∈
      compactSupportSections f F W :=
  sorry

/-- Restriction of compactly supported sections along a morphism of étale
`Y`-schemes. -/
def compactSupportSectionsRestrict
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V W : Y.Etale}
    (g : W ⟶ V) :
    compactSupportSections f F V →+ compactSupportSections f F W :=
  (((F.obj.map ((smallEtalePullback f).map g).op).hom.comp
        (compactSupportSections f F V).subtype).codRestrict
    (compactSupportSections f F W)
    (restrict_mem_compactSupportSections f F g))

/-- A morphism of abelian étale sheaves preserves proper support of
sections. -/
theorem sheafHom_mem_compactSupportSections
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    (V : Y.Etale) (σ : compactSupportSections f F V) :
    (α.hom.app (op ((smallEtalePullback f).obj V)))
        ((compactSupportSections f F V).subtype σ) ∈
      compactSupportSections f G V :=
  sorry

/-- The map on compactly supported sections induced by a morphism of abelian
étale sheaves. -/
def compactSupportSectionsSheafHom
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    (V : Y.Etale) :
    compactSupportSections f F V →+ compactSupportSections f G V :=
  (((α.hom.app (op ((smallEtalePullback f).obj V))).hom.comp
        (compactSupportSections f F V).subtype).codRestrict
    (compactSupportSections f G V)
    (sheafHom_mem_compactSupportSections f α V))

/-- Restriction of compactly supported sections along an identity is the identity. -/
theorem compactSupportSectionsRestrict_id
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etaleᵒᵖ) :
    AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F (𝟙 V).unop) =
      𝟙 (AddCommGrpCat.of (compactSupportSections f F V.unop)) := sorry

/-- Restriction of compactly supported sections respects composition. -/
theorem compactSupportSectionsRestrict_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {U V W : Y.Etaleᵒᵖ}
    (g : U ⟶ V) (h : V ⟶ W) :
    AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F (g ≫ h).unop) =
      AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F g.unop) ≫
        AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F h.unop) := sorry

/-- The maps on compactly supported sections induced by a sheaf morphism commute
with restriction. -/
theorem compactSupportSectionsSheafHom_restrict
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    {V W : Y.Etaleᵒᵖ} (g : V ⟶ W) :
    AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F g.unop) ≫
        AddCommGrpCat.ofHom (compactSupportSectionsSheafHom f α W.unop) =
      AddCommGrpCat.ofHom (compactSupportSectionsSheafHom f α V.unop) ≫
        AddCommGrpCat.ofHom (compactSupportSectionsRestrict f G g.unop) := sorry

/-- The compact-support presheaf of an abelian étale sheaf, sending `V` to the
group of sections of `F` on `X_V` with support proper over `V`. -/
def etaleLowerShriekPresheaf (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (compactSupportSections f F V.unop)
  map g := AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F g.unop)
  map_id := compactSupportSectionsRestrict_id f F
  map_comp := compactSupportSectionsRestrict_comp f F

/-- A morphism of abelian étale sheaves induces a morphism of compact-support
presheaves. -/
def etaleLowerShriekPresheafMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekPresheaf f F ⟶ etaleLowerShriekPresheaf f G where
  app V := AddCommGrpCat.ofHom (compactSupportSectionsSheafHom f α V.unop)
  naturality := fun _ _ g => compactSupportSectionsSheafHom_restrict f α g

/-- The compact-support presheaf is a sheaf on the small étale site of `Y`. -/
theorem etaleLowerShriekPresheaf_isSheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Presheaf.IsSheaf Y.smallEtaleTopology (etaleLowerShriekPresheaf f F) :=
  sorry

/-- The abelian étale sheaf of sections with support proper over the base. -/
def etaleLowerShriekObj (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  ⟨etaleLowerShriekPresheaf f F, etaleLowerShriekPresheaf_isSheaf f F⟩

/-- The morphism of compact-support sheaves induced by a morphism of coefficient sheaves. -/
def etaleLowerShriekMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekObj f F ⟶ etaleLowerShriekObj f G :=
  ObjectProperty.homMk (etaleLowerShriekPresheafMap f α)

/-- The map on compact-support sheaves induced by an identity is the identity. -/
theorem etaleLowerShriekMap_id (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekMap f (𝟙 F) = 𝟙 (etaleLowerShriekObj f F) := sorry

/-- The maps on compact-support sheaves respect composition of coefficient morphisms. -/
theorem etaleLowerShriekMap_comp
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) (β : G ⟶ H) :
    etaleLowerShriekMap f (α ≫ β) =
      etaleLowerShriekMap f α ≫ etaleLowerShriekMap f β := sorry

/-- Direct image with compact support `f_!` on abelian sheaves on the small étale
site, for a separated locally finite-type morphism. -/
def etaleLowerShriek :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj := etaleLowerShriekObj f
  map := etaleLowerShriekMap f
  map_id := etaleLowerShriekMap_id f
  map_comp := etaleLowerShriekMap_comp f

/-- The value of `etaleLowerShriek` at an étale `Y`-scheme is the group of
compactly supported sections. -/
theorem etaleLowerShriek_obj (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    ((etaleLowerShriek f).obj F).obj.obj (op V) =
      AddCommGrpCat.of (compactSupportSections f F V) :=
  sorry

/-- Inclusion of compactly supported sections into all sections commutes with restriction. -/
theorem compactSupportSectionsSubtype_restrict
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V W : Y.Etaleᵒᵖ}
    (g : V ⟶ W) :
    AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F g.unop) ≫
        AddCommGrpCat.ofHom (compactSupportSections f F W.unop).subtype =
      AddCommGrpCat.ofHom (compactSupportSections f F V.unop).subtype ≫
        F.obj.map ((smallEtalePullback f).map g.unop).op := sorry

/-- The inclusion of the compact-support sheaf into the ordinary étale direct image. -/
def etaleLowerShriekιApp (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekObj f F ⟶
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology).obj F :=
  ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom (compactSupportSections f F V.unop).subtype
      naturality := fun _ _ g => compactSupportSectionsSubtype_restrict f F g }

/-- The compact-support inclusion is natural in the coefficient sheaf. -/
theorem etaleLowerShriekιApp_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekMap f α ≫ etaleLowerShriekιApp f G =
      etaleLowerShriekιApp f F ≫
        ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).map α := sorry

/-- The canonical inclusion `f_! ⟶ f_*` of the compact-support subfunctor into
ordinary small-étale pushforward. -/
def etaleLowerShriekι :
    etaleLowerShriek f ⟶
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology where
  app := etaleLowerShriekιApp f
  naturality := fun _ _ α => etaleLowerShriekιApp_naturality f α

/-- The compact-support inclusion acts on sections by the subgroup subtype. -/
theorem etaleLowerShriekι_app_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V) :
    ((etaleLowerShriekι f).app F).hom.app (op V) σ =
      (compactSupportSections f F V).subtype σ :=
  sorry

/-- A pushforward section lies in the image of `etaleLowerShriekι` if and only
if it has proper support over the base. -/
theorem mem_range_etaleLowerShriekι_app_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    (∃ τ : compactSupportSections f F V,
        ((etaleLowerShriekι f).app F).hom.app (op V) τ = σ) ↔
      HasProperSupport f F V σ :=
  sorry

/-- The compact-support inclusion `f_! ⟶ f_*` is a monomorphism. -/
instance etaleLowerShriekι_mono : Mono (etaleLowerShriekι f) := sorry

end AlgebraicGeometry.Scheme.Etale

end
