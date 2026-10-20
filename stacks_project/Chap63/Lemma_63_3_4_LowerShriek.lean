module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

#check (HasProperSupport f :
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) → (V : Y.Etale) →
    F.obj.obj (op ((smallEtalePullback f).obj V)) → Prop)

#check (hasProperSupport_iff f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))),
    HasProperSupport f F V σ ↔
      ClosedSubset.IsProperOver (pullback.fst V.hom f)
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ))

variable [LocallyOfFiniteType f]

/-- Membership in the compact-support subgroup is the proper-support condition. -/
abbrev mem_compactSupportSections_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    σ ∈ compactSupportSections f F V ↔ HasProperSupport f F V σ :=
  mem_properSupportSections_iff f F V σ

#check (compactSupportSections f :
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) → (V : Y.Etale) →
    AddSubgroup (F.obj.obj (op ((smallEtalePullback f).obj V))))

#check (mem_properSupportSections_iff f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))),
    σ ∈ compactSupportSections f F V ↔ HasProperSupport f F V σ)

variable [IsSeparated f]

#check (restrict_mem_compactSupportSections f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V W : Y.Etale}
    (g : W ⟶ V) (σ : compactSupportSections f F V),
    (F.obj.map ((smallEtalePullback f).map g).op)
        ((compactSupportSections f F V).subtype σ) ∈
      compactSupportSections f F W)

#check (compactSupportSectionsRestrict f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V W : Y.Etale}
    (g : W ⟶ V), compactSupportSections f F V →+ compactSupportSections f F W)

#check (sheafHom_mem_compactSupportSections f :
  ∀ {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    (V : Y.Etale) (σ : compactSupportSections f F V),
    (α.hom.app (op ((smallEtalePullback f).obj V)))
        ((compactSupportSections f F V).subtype σ) ∈
      compactSupportSections f G V)

#check (compactSupportSectionsSheafHom f :
  ∀ {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    (V : Y.Etale), compactSupportSections f F V →+ compactSupportSections f G V)

#check (etaleLowerShriekPresheaf f :
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u} → Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})

#check (etaleLowerShriekPresheafMap f :
  ∀ {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G),
    etaleLowerShriekPresheaf f F ⟶ etaleLowerShriekPresheaf f G)

#check (etaleLowerShriekPresheaf_isSheaf f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    Presheaf.IsSheaf Y.smallEtaleTopology (etaleLowerShriekPresheaf f F))

#check (etaleLowerShriek f :
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

#check (etaleLowerShriek_obj f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale),
    ((etaleLowerShriek f).obj F).obj.obj (op V) =
      AddCommGrpCat.of (compactSupportSections f F V))

#check (etaleLowerShriekι f :
  etaleLowerShriek f ⟶
    (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)

#check (etaleLowerShriekι_app_apply f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections f F V),
    ((etaleLowerShriekι f).app F).hom.app (op V) σ =
      (compactSupportSections f F V).subtype σ)

#check (mem_range_etaleLowerShriekι_app_iff f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))),
    (∃ τ : compactSupportSections f F V,
      ((etaleLowerShriekι f).app F).hom.app (op V) τ = σ) ↔
      HasProperSupport f F V σ)

#check (etaleLowerShriekι_mono f : Mono (etaleLowerShriekι f))

end AlgebraicGeometry.Scheme.Etale
