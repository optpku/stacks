module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SupportExcision
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

/-!
# Covariance of compact-support étale pushforward along open immersions

For a separated locally finite-type morphism `f : X ⟶ Y` and an open immersion
`j : X' ⟶ X`, there is a canonical injective comparison
`f'_!(F|_{X'}) ⟶ f_! F` of underived compact-support pushforwards, obtained by
unique extension of properly supported sections from `X'_V` to `X_V`.
-/

public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y) [IsOpenImmersion j]

/-- The morphism of small étale sites `X'_V ⟶ X_V` induced by an open immersion
of the source over `Y`. -/
def openImmersionPullback :
    smallEtalePullback (j ≫ f) ⋙ etaleRestriction j ⟶ smallEtalePullback f :=
  MorphismProperty.Over.pullbackMapHomPullback (P := @Etale)
    (Q := (⊤ : MorphismProperty Scheme)) j inferInstance trivial f

/-- The scheme morphism underlying `openImmersionPullback` at `V` is an open
immersion `X'_V ⟶ X_V`. -/
theorem isOpenImmersion_openImmersionPullback_app (V : Y.Etale) :
    IsOpenImmersion ((openImmersionPullback j f).app V).left :=
  sorry

/-- Precomposition with `openImmersionPullback` is continuous for the small
étale topologies. -/
instance openImmersionPullback_isContinuous :
    (smallEtalePullback (j ≫ f) ⋙ etaleRestriction j).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (smallEtalePullback (j ≫ f)) (etaleRestriction j)
    Y.smallEtaleTopology X'.smallEtaleTopology X.smallEtaleTopology

/-- Restriction of ordinary small-étale pushforward along an open immersion of
the source: the bottom arrow `f_* F ⟶ f'_*(F|_{X'})`. -/
def etaleAbelianPushforwardRestrict :
    (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology ⟶
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        (smallEtalePullback (j ≫ f)).sheafPushforwardContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology X'.smallEtaleTopology :=
  sheafPushforwardContinuousNatTrans (openImmersionPullback j f) AddCommGrpCat.{u}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Sections of `F|_{X'}` on `X'_V` agree with sections of `F` on the image of
`X'_V` in `X.Etale`. -/
theorem etaleRestrictionSheaf_obj_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F).obj.obj
        (op ((smallEtalePullback (j ≫ f)).obj V)) =
      F.obj.obj
        (op ((etaleRestriction j).obj ((smallEtalePullback (j ≫ f)).obj V))) :=
  rfl

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y) [IsOpenImmersion j]
variable [IsSeparated f] [LocallyOfFiniteType f]

/-- The reduced closed-subscheme structure on the support of a compactly
supported section of `F|_{X'}` over an étale `Y`-scheme. -/
private def compactSupportSectionStructure
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    ClosedSubschemeStructure
      (abelianSheafSectionSupport
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F)
        ((smallEtalePullback (j ≫ f)).obj V)
        ((compactSupportSections (j ≫ f)
            ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V).subtype σ)) :=
  ClosedSubschemeStructure.reduced _

/-- The support of a compactly supported section of `F|_{X'}` remains a closed
immersion after composing with the base change of the open immersion. -/
private theorem isClosedImmersion_support_openImmersion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    IsClosedImmersion
      ((compactSupportSectionStructure j f F V σ).ι ≫
        ((openImmersionPullback j f).app V).left) :=
  sorry

/-- The reduced support of a compactly supported section is a closed
immersion into `X'_V`. -/
private theorem isClosedImmersion_compactSupportSectionStructure_ι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    IsClosedImmersion (compactSupportSectionStructure j f F V σ).ι :=
  inferInstanceAs
    (IsClosedImmersion (compactSupportSectionStructure j f F V σ).ideal.subschemeι)

/-- A compactly supported section of `F|_{X'}` on `X'_V` is supported in the
image of its reduced support subscheme. -/
private theorem compactSupportSections_mem_supportedIn
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    ((compactSupportSections (j ≫ f)
          ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V).subtype σ) ∈
      abelianSheafSectionsSupportedIn F
        ((etaleRestriction j).obj ((smallEtalePullback (j ≫ f)).obj V))
        (Set.range (compactSupportSectionStructure j f F V σ).ι) :=
  sorry

/-- The unique extension of a compactly supported section from `X'_V` to a
section of `F` on `X_V`. -/
private def extendCompactSupportSection
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    F.obj.obj (op ((smallEtalePullback f).obj V)) :=
  (@extendSupportedAlongOpen _ F _ _
      ((openImmersionPullback j f).app V) _
      (compactSupportSectionStructure j f F V σ).ι
      (isClosedImmersion_compactSupportSectionStructure_ι j f F V σ)
      (isClosedImmersion_support_openImmersion j f F V σ)
      ⟨(compactSupportSections (j ≫ f)
            ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V).subtype σ,
        compactSupportSections_mem_supportedIn j f F V σ⟩).val

/-- The extended section on `X_V` has support proper over `V`. -/
private theorem hasProperSupport_extendSupportedAlongOpen
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    HasProperSupport f F V (extendCompactSupportSection j f F V σ) :=
  sorry

/-- Extension of the zero compactly supported section is zero. -/
private theorem compactSupportSectionsOpenImmersion_map_zero
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    extendCompactSupportSection j f F V 0 = 0 := sorry

/-- Extension of compactly supported sections preserves addition. -/
private theorem compactSupportSectionsOpenImmersion_map_add
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ τ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    extendCompactSupportSection j f F V (σ + τ) =
      extendCompactSupportSection j f F V σ + extendCompactSupportSection j f F V τ :=
  sorry

/-- Sectionwise covariance map: extend a compactly supported section of
`F|_{X'}` on `X'_V` uniquely to a compactly supported section of `F` on
`X_V`. -/
def compactSupportSectionsOpenImmersion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    compactSupportSections (j ≫ f)
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V →+
      compactSupportSections f F V := by
  exact
    { toFun := fun σ ↦
        ⟨extendCompactSupportSection j f F V σ,
          (mem_properSupportSections_iff f F V
              (extendCompactSupportSection j f F V σ)).mpr
            (hasProperSupport_extendSupportedAlongOpen j f F V σ)⟩
      map_zero' := Subtype.ext (compactSupportSectionsOpenImmersion_map_zero j f F V)
      map_add' := fun σ τ ↦
        Subtype.ext (compactSupportSectionsOpenImmersion_map_add j f F V σ τ) }

/-- Restriction of the extended compactly supported section recovers the
original section on `X'_V`. -/
theorem compactSupportSectionsOpenImmersion_restrict
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    ((etaleAbelianPushforwardRestrict j f).app F).hom.app (op V)
        ((compactSupportSections f F V).subtype
          (compactSupportSectionsOpenImmersion j f F V σ)) =
      (compactSupportSections (j ≫ f)
          ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V).subtype σ :=
  sorry

/-- Extension of compactly supported sections commutes with étale restriction. -/
theorem compactSupportSectionsOpenImmersion_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V W : Y.Etaleᵒᵖ} (g : V ⟶ W) :
    (etaleLowerShriekPresheaf (j ≫ f)
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F)).map g ≫
      AddCommGrpCat.ofHom (compactSupportSectionsOpenImmersion j f F W.unop) =
    AddCommGrpCat.ofHom (compactSupportSectionsOpenImmersion j f F V.unop) ≫
      (etaleLowerShriekPresheaf f F).map g := sorry

/-- Extension of compactly supported sections commutes with morphisms of abelian sheaves. -/
theorem etaleLowerShriekOpenImmersion_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekPresheafMap (j ≫ f)
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).map α) ≫
      ({ app := fun V ↦ AddCommGrpCat.ofHom
           (compactSupportSectionsOpenImmersion j f G V.unop)
         naturality := fun V W g ↦ compactSupportSectionsOpenImmersion_naturality j f G g } :
        etaleLowerShriekPresheaf (j ≫ f)
            ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G) ⟶
          etaleLowerShriekPresheaf f G) =
    ({ app := fun V ↦ AddCommGrpCat.ofHom
           (compactSupportSectionsOpenImmersion j f F V.unop)
       naturality := fun V W g ↦ compactSupportSectionsOpenImmersion_naturality j f F g } :
      etaleLowerShriekPresheaf (j ≫ f)
          ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) ⟶
        etaleLowerShriekPresheaf f F) ≫
      etaleLowerShriekPresheafMap f α := sorry

/-- Canonical covariance `f'_!(F|_{X'}) ⟶ f_! F` of underived compact-support
pushforwards along an open immersion of the source, as a natural
transformation in the abelian sheaf `F`. -/
@[expose] def etaleLowerShriekOpenImmersion :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ etaleLowerShriek (j ≫ f) ⟶
      etaleLowerShriek f where
  app F :=
    ObjectProperty.homMk
      { app := fun V ↦
          AddCommGrpCat.ofHom (compactSupportSectionsOpenImmersion j f F V.unop)
        naturality := fun V W g ↦
          compactSupportSectionsOpenImmersion_naturality j f F g }
  naturality := fun F G α ↦
    ObjectProperty.hom_ext _ (etaleLowerShriekOpenImmersion_naturality j f α)

/-- The covariance comparison acts on sections by
`compactSupportSectionsOpenImmersion`. -/
theorem etaleLowerShriekOpenImmersion_app_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    ((etaleLowerShriekOpenImmersion j f).app F).hom.app (op V) σ =
      compactSupportSectionsOpenImmersion j f F V σ :=
  rfl

/-- The covariance comparison `f'_!(F|_{X'}) ⟶ f_! F` is a monomorphism. -/
instance etaleLowerShriekOpenImmersion_app_mono
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Mono ((etaleLowerShriekOpenImmersion j f).app F) :=
  sorry

/-- The covariance comparison fills the triangle with compact-support
inclusions and restriction of ordinary pushforwards. -/
theorem etaleLowerShriekOpenImmersion_ι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekOpenImmersion j f).app F ≫
        (etaleLowerShriekι f).app F ≫
          (etaleAbelianPushforwardRestrict j f).app F =
      (etaleLowerShriekι (j ≫ f)).app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) :=
  sorry

/-- Restriction along a composite open immersion is the composite of the
site-level restriction functors. -/
def etaleRestrictionCompIso_open {X'' : Scheme.{u}} (j' : X'' ⟶ X')
    [IsOpenImmersion j'] :
    etaleRestriction (j' ≫ j) ≅ etaleRestriction j' ⋙ etaleRestriction j :=
  MorphismProperty.Over.mapComp (P := @Etale)
    (Q := (⊤ : MorphismProperty Scheme))
    (inferInstance : Etale j') (inferInstance : Etale j) (j' ≫ j) rfl

/-- Restriction of abelian small-étale sheaves along a composite open immersion
is the composite of the restrictions. -/
def etaleAbelianRestrictionSheafCompIso {X'' : Scheme.{u}} (j' : X'' ⟶ X')
    [IsOpenImmersion j'] :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        etaleRestrictionSheaf j' AddCommGrpCat.{u} ≅
      etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u} :=
  sheafPushforwardContinuousComp' (etaleRestrictionCompIso_open j j').symm
    AddCommGrpCat.{u} X''.smallEtaleTopology X'.smallEtaleTopology
    X.smallEtaleTopology

/-- Compact-support pushforward is unchanged when the scheme morphism is
replaced by an equal morphism. -/
def etaleLowerShriekCongr {X Y : Scheme.{u}} {g h : X ⟶ Y}
    [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h]
    (e : g = h) : etaleLowerShriek g ≅ etaleLowerShriek h :=
  eqToIso (e ▸ rfl)

/-- Covariance along nested open immersions `X'' ⟶ X' ⟶ X` is the composite of
the two covariance maps. -/
theorem etaleLowerShriekOpenImmersion_comp {X'' : Scheme.{u}} (j' : X'' ⟶ X')
    [IsOpenImmersion j'] :
    whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (etaleLowerShriekOpenImmersion j' (j ≫ f)) ≫
        etaleLowerShriekOpenImmersion j f =
      whiskerRight (etaleAbelianRestrictionSheafCompIso j j').hom
          (etaleLowerShriek (j' ≫ j ≫ f)) ≫
        whiskerLeft (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u})
          (etaleLowerShriekCongr (Category.assoc j' j f).symm).hom ≫
          etaleLowerShriekOpenImmersion (j' ≫ j) f :=
  sorry

/-- Covariance of compact-support pushforward along the open immersion of a
Zariski open subscheme. -/
abbrev etaleLowerShriekOpenImmersion_opens {X Y : Scheme.{u}} (U : X.Opens)
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] :
    etaleRestrictionSheaf U.ι AddCommGrpCat.{u} ⋙ etaleLowerShriek (U.ι ≫ f) ⟶
      etaleLowerShriek f :=
  etaleLowerShriekOpenImmersion U.ι f

end AlgebraicGeometry.Scheme.Etale

end
