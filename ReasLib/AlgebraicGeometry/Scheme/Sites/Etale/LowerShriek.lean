/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport

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

/-- A section of `F` on the small-étale pullback `X_V` has proper support over
`V` when the closed support of the section is proper over `V`. This is the
sectionwise condition cutting out `f_! F ⊂ f_* F`. -/
def HasProperSupport (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) : Prop :=
  ClosedSubset.IsProperOver (pullback.fst V.hom f)
    (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)

/-- Proper support of a pushforward section is properness of its étale section
support over the base. -/
theorem hasProperSupport_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasProperSupport f F V σ ↔
      ClosedSubset.IsProperOver (pullback.fst V.hom f)
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ) :=
  sorry

/-- The additive subgroup of sections of `F` on `X_V` whose support is proper
over `V`. These are the sections of `f_! F` over `V`. -/
def compactSupportSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    AddSubgroup (F.obj.obj (op ((smallEtalePullback f).obj V))) where
  carrier := {σ | HasProperSupport f F V σ}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the compact-support subgroup is proper support of the
section. -/
theorem mem_compactSupportSections_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    σ ∈ compactSupportSections f F V ↔ HasProperSupport f F V σ :=
  sorry

variable [IsSeparated f] [LocallyOfFiniteType f]

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

/-- The compact-support presheaf of an abelian étale sheaf, sending `V` to the
group of sections of `F` on `X_V` with support proper over `V`. -/
def etaleLowerShriekPresheaf (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (compactSupportSections f F V.unop)
  map g := AddCommGrpCat.ofHom (compactSupportSectionsRestrict f F g.unop)
  map_id := sorry
  map_comp := sorry

/-- A morphism of abelian étale sheaves induces a morphism of compact-support
presheaves. -/
def etaleLowerShriekPresheafMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekPresheaf f F ⟶ etaleLowerShriekPresheaf f G where
  app V := AddCommGrpCat.ofHom (compactSupportSectionsSheafHom f α V.unop)
  naturality := sorry

/-- The compact-support presheaf is a sheaf on the small étale site of `Y`. -/
theorem etaleLowerShriekPresheaf_isSheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Presheaf.IsSheaf Y.smallEtaleTopology (etaleLowerShriekPresheaf f F) :=
  sorry

/-- Direct image with compact support `f_!` on abelian sheaves on the small étale
site, for a separated locally finite-type morphism. -/
def etaleLowerShriek :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj F := ⟨etaleLowerShriekPresheaf f F, etaleLowerShriekPresheaf_isSheaf f F⟩
  map α := ObjectProperty.homMk (etaleLowerShriekPresheafMap f α)
  map_id := sorry
  map_comp := sorry

/-- The value of `etaleLowerShriek` at an étale `Y`-scheme is the group of
compactly supported sections. -/
theorem etaleLowerShriek_obj (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    ((etaleLowerShriek f).obj F).obj.obj (op V) =
      AddCommGrpCat.of (compactSupportSections f F V) :=
  sorry

/-- The canonical inclusion `f_! ⟶ f_*` of the compact-support subfunctor into
ordinary small-étale pushforward. -/
def etaleLowerShriekι :
    etaleLowerShriek f ⟶
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology where
  app F :=
    ObjectProperty.homMk
      { app := fun V ↦
          AddCommGrpCat.ofHom (compactSupportSections f F V.unop).subtype
        naturality := sorry }
  naturality := sorry

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
