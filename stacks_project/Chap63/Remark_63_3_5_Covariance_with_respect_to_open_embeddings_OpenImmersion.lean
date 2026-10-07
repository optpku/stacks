module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap63.Lemma_63_2_1
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

/-!
# Covariance of compact-support étale pushforward along open immersions

For a separated locally finite-type morphism `f : X ⟶ Y` and an open immersion
`j : X' ⟶ X`, there is a canonical injective comparison
`f'_!(F|_{X'}) ⟶ f_! F` of underived compact-support pushforwards, obtained by
unique extension of properly supported sections from `X'_V` to `X_V`.
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
    etaleAbelianPushforward f ⟶
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ etaleAbelianPushforward (j ≫ f) :=
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
  sorry

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- Unique extension of sections supported on a closed subscheme along a
morphism of small étale objects, via the inverse of
`abelianSheafSectionsSupportedInAddEquiv`. -/
def extendSupportedAlongOpen {U U' : X.Etale} (φ : U' ⟶ U) {Z' : Scheme.{u}}
    (ι : Z' ⟶ U'.left) [IsClosedImmersion ι]
    (h_closed : IsClosedImmersion (ι ≫ φ.left)) :
    abelianSheafSectionsSupportedIn F U' (Set.range ι) →+
      abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) :=
  AddEquiv.toAddMonoidHom
    (@abelianSheafSectionsSupportedInAddEquiv _ F _ _ φ _ ι inferInstance
      h_closed).symm

/-- Unique extension along an open acts by the inverse supported-section
equivalence. -/
theorem extendSupportedAlongOpen_apply {U U' : X.Etale} (φ : U' ⟶ U)
    {Z' : Scheme.{u}} (ι : Z' ⟶ U'.left) [IsClosedImmersion ι]
    (h_closed : IsClosedImmersion (ι ≫ φ.left))
    (σ : abelianSheafSectionsSupportedIn F U' (Set.range ι)) :
    extendSupportedAlongOpen F φ ι h_closed σ =
      (@abelianSheafSectionsSupportedInAddEquiv _ F _ _ φ _ ι inferInstance
        h_closed).symm σ :=
  sorry

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y) [IsOpenImmersion j]
variable [IsSeparated f] [LocallyOfFiniteType f]

/-- The reduced closed-subscheme structure on the support of a compactly
supported section of `F|_{X'}` over an étale `Y`-scheme. -/
def compactSupportSectionStructure
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
immersion after composing with `X'_V ⟶ X_V`, by Cohomology of Schemes,
Lemma 30.26.5. -/
theorem isClosedImmersion_support_openImmersion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    IsClosedImmersion
      ((compactSupportSectionStructure j f F V σ).ι ≫
        ((openImmersionPullback j f).app V).left) :=
  sorry

/-- The reduced support of a compactly supported section is a closed
immersion into `X'_V`. -/
instance isClosedImmersion_compactSupportSectionStructure_ι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    IsClosedImmersion (compactSupportSectionStructure j f F V σ).ι :=
  inferInstanceAs
    (IsClosedImmersion (compactSupportSectionStructure j f F V σ).ideal.subschemeι)

/-- A compactly supported section of `F|_{X'}` on `X'_V` is supported in the
image of its reduced support subscheme. -/
theorem compactSupportSections_mem_supportedIn
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
def extendCompactSupportSection
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
theorem hasProperSupport_extendSupportedAlongOpen
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    HasProperSupport f F V (extendCompactSupportSection j f F V σ) :=
  sorry

/-- Sectionwise covariance map: extend a compactly supported section of
`F|_{X'}` on `X'_V` uniquely to a compactly supported section of `F` on
`X_V`. -/
def compactSupportSectionsOpenImmersion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    compactSupportSections (j ≫ f)
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V →+
      compactSupportSections f F V where
  toFun σ :=
    ⟨extendCompactSupportSection j f F V σ,
      (mem_compactSupportSections_iff f F V
          (extendCompactSupportSection j f F V σ)).mpr
        (hasProperSupport_extendSupportedAlongOpen j f F V σ)⟩
  map_zero' := sorry
  map_add' := sorry

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

/-- Canonical covariance `f'_!(F|_{X'}) ⟶ f_! F` of underived compact-support
pushforwards along an open immersion of the source, as a natural
transformation in the abelian sheaf `F`. -/
def etaleLowerShriekOpenImmersion :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ etaleLowerShriek (j ≫ f) ⟶
      etaleLowerShriek f where
  app F :=
    ObjectProperty.homMk
      { app := fun V ↦
          AddCommGrpCat.ofHom (compactSupportSectionsOpenImmersion j f F V.unop)
        naturality := sorry }
  naturality := sorry

/-- The covariance comparison acts on sections by
`compactSupportSectionsOpenImmersion`. -/
theorem etaleLowerShriekOpenImmersion_app_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : compactSupportSections (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    ((etaleLowerShriekOpenImmersion j f).app F).hom.app (op V) σ =
      compactSupportSectionsOpenImmersion j f F V σ :=
  sorry

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
