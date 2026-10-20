module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [Ring Λ]
variable [LocallyOfFiniteType f] [IsSeparated f]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Scalar multiplication preserves proper support of a section of an étale module sheaf. -/
theorem moduleProperSupportSections_smul
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale)
    (r : Λ) (σ : F.obj.obj (op ((smallEtalePullback f).obj V)))
    (hσ : HasProperSupport f
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) V σ) :
    HasProperSupport f
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) V (r • σ) := sorry

/-- The submodule of direct-image sections whose support is proper over the étale base. -/
def moduleProperSupportSections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale) :
    Submodule Λ (F.obj.obj (op ((smallEtalePullback f).obj V))) where
  toAddSubmonoid := (properSupportSections f
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) V).toAddSubmonoid
  smul_mem' := fun r σ hσ => moduleProperSupportSections_smul f Λ F V r σ hσ

/-- A module section belongs to the proper-support submodule exactly when its support is proper. -/
theorem mem_moduleProperSupportSections_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    σ ∈ moduleProperSupportSections f Λ F V ↔
      HasProperSupport f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) V σ := Iff.rfl

/-- The presheaf of module sections with support proper over the base. -/
def etaleModuleLowerShriekPresheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj V := ModuleCat.of Λ (moduleProperSupportSections f Λ F V.unop)
  map {V W} g := ModuleCat.ofHom
    (((F.obj.map ((smallEtalePullback f).map g.unop).op).hom.comp
        (moduleProperSupportSections f Λ F V.unop).subtype).codRestrict
      (moduleProperSupportSections f Λ F W.unop)
      (fun σ => restrict_mem_compactSupportSections f
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)
        g.unop ⟨σ.val, σ.property⟩))
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro σ
    apply Subtype.ext
    change (F.obj.map ((smallEtalePullback f).map (𝟙 V).unop).op) σ.val = σ.val
    simp
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro σ
    apply Subtype.ext
    change (F.obj.map ((smallEtalePullback f).map (g ≫ h).unop).op) σ.val =
      (F.obj.map ((smallEtalePullback f).map h.unop).op)
        ((F.obj.map ((smallEtalePullback f).map g.unop).op) σ.val)
    simp

/-- Module sections with proper support form a sheaf on the small étale site of the base. -/
theorem etaleModuleLowerShriekPresheaf_isSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Presheaf.IsSheaf Y.smallEtaleTopology (etaleModuleLowerShriekPresheaf f Λ F) := sorry

/-- Direct image with proper support for module sheaves along a separated locally finite-type map. -/
def etaleModuleLowerShriek :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) where
  obj F := ⟨etaleModuleLowerShriekPresheaf f Λ F,
    etaleModuleLowerShriekPresheaf_isSheaf f Λ F⟩
  map {F G} α := ObjectProperty.homMk
    { app := fun V => ModuleCat.ofHom
        (((α.hom.app (op ((smallEtalePullback f).obj V.unop))).hom.comp
            (moduleProperSupportSections f Λ F V.unop).subtype).codRestrict
          (moduleProperSupportSections f Λ G V.unop)
          (fun σ => sheafHom_mem_compactSupportSections f
            ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map α)
            V.unop ⟨σ.val, σ.property⟩))
      naturality := fun V W g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro σ
        apply Subtype.ext
        exact ConcreteCategory.congr_hom
          (α.hom.naturality ((smallEtalePullback f).map g.unop).op) σ.val }
  map_id F := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro σ
    apply Subtype.ext
    rfl
  map_comp α β := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro σ
    apply Subtype.ext
    rfl

/-- Sections of module direct image with proper support are exactly the proper-support submodule. -/
theorem etaleModuleLowerShriek_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (V : Y.Etale) :
    ((etaleModuleLowerShriek f Λ).obj F).obj.obj (op V) =
      ModuleCat.of Λ (moduleProperSupportSections f Λ F V) := rfl

variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]

/-- Proper-support direct image along a separated locally quasi-finite map is additive. -/
instance etaleModuleLowerShriek_additive [LocallyQuasiFinite f] :
    (etaleModuleLowerShriek f Λ).Additive := sorry

/-- Proper-support direct image along a separated locally quasi-finite map preserves finite limits. -/
instance etaleModuleLowerShriek_preservesFiniteLimits [LocallyQuasiFinite f] :
    PreservesFiniteLimits (etaleModuleLowerShriek f Λ) := sorry

/-- Proper-support direct image along a separated locally quasi-finite map preserves finite colimits. -/
instance etaleModuleLowerShriek_preservesFiniteColimits [LocallyQuasiFinite f] :
    PreservesFiniteColimits (etaleModuleLowerShriek f Λ) := sorry

end AlgebraicGeometry.Scheme.Etale

end
