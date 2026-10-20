module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.BaseChange.Basic
public import stacks_project.Chap20.«20_14_1_1»
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange.OfSites
public import stacks_project.Chap20.Lemma_20_32_2
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived.Notation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped RingedSpace.Hom RingedSpaceDerivedPushforward RingedSpaceDerivedRestriction

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.4:
- primary domain: restriction to open subspaces and derived direct image for `𝒪_X`-module
  sheaves on ringed spaces;
- sampled owner declarations:
  `moduleDerivedPushforward`,
  `openSubspaceModuleCategory`,
  `moduleRestrictionToOpenDerived`,
  `restrictedMorphismToOpen`;
- best owner abstraction:
  `source-facing`: the objectwise comparison
  `moduleDerivedPushforward_restrict_obj_isomorphic`, expressing the source statement
  `(R(f)_* E)|_V = R(g)_*(E|_U)` for `E : D(𝒪_X)`;
  `core/canonical`: `moduleDerivedPushforward`, `openSubspaceModuleCategory`,
  `moduleRestrictionToOpenDerived`, `restrictedMorphismToOpen`, and the functor-level companion
  `moduleDerivedPushforward_restrict_isomorphic`;
  `bridge/view`: `restrictedModuleDerivedOnOpen`, which views restriction inside the intrinsic
  derived category of the restricted ringed space and keeps the source-facing theorem in the
  intrinsic derived category on the open subspaces.
- primitive data: the morphism `f : X ⟶ Y` and the open `V ⊆ Y`;
- derived API: the functor-level `IsIsomorphic` comparison below and its objectwise companion.
-/

variable {X Y : RingedSpace.{u}}

section

variable (f : X ⟶ Y) (V : Opens Y.carrier)

local notation "DModX" => DerivedCategory X.Modules
local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "QisX" => HomologicalComplex.quasiIso ModX (ComplexShape.up ℤ)
local notation "U" => preimageOpen f V
local notation "g" => restrictedMorphismToOpen f V
local notation "DResX" => moduleRestrictionToOpenDerived X U
local notation "DResY" => moduleRestrictionToOpenDerived Y V

local instance ringedSpaceModules_categoryWithHomology_local
    (Z : RingedSpace.{u}) :
    CategoryWithHomology (RingedSpace.Modules Z) :=
  ringedSpaceModules_categoryWithHomology Z

local instance ringedSpaceModules_Q_isLocalization_local
    (Z : RingedSpace.{u}) :
    Functor.IsLocalization
      (DerivedCategory.Q :
        CochainComplex (RingedSpace.Modules Z) ℤ ⥤
          DerivedCategory (RingedSpace.Modules Z))
      (HomologicalComplex.quasiIso (RingedSpace.Modules Z) (ComplexShape.up ℤ)) :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

local instance openSubspaceModuleCategory_Q_isLocalization_local
    (Z : RingedSpace.{u}) (W : Opens Z.carrier) :
    Functor.IsLocalization
      (DerivedCategory.Q :
        CochainComplex (openSubspaceModuleCategory Z W) ℤ ⥤
          DerivedCategory (openSubspaceModuleCategory Z W))
      (HomologicalComplex.quasiIso (openSubspaceModuleCategory Z W) (ComplexShape.up ℤ)) :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

/-- Helper for Lemma 20.32.4: after pushing forward from `V` back to `Y`, the pushforward along
`g : U ⟶ V` matches open pushforward from `U` followed by `f_*`. -/
noncomputable def restrictedPushforward_postcomposeOpenIso :
    moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g ⋙ modulePushforwardFromOpen V ≅
      moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U ⋙ RingedSpace.Hom.pushforward f :=
  let iU : X.restrict (preimageOpen f V).isOpenEmbedding ⟶ X :=
    X.ofRestrict (preimageOpen f V).isOpenEmbedding
  let iV : Y.restrict V.isOpenEmbedding ⟶ Y := Y.ofRestrict V.isOpenEmbedding
  let hfac : g ≫ iV = iU ≫ f := restrictedMorphismToOpen_fac (f := f) (V := V)
  let hpush :
      RingedSpace.Hom.pushforward (g ≫ iV) ≅
        RingedSpace.Hom.pushforward (iU ≫ f) :=
    eqToIso (congrArg RingedSpace.Hom.pushforward hfac)
  let compIso :
      RingedSpace.Hom.pushforward g ⋙ modulePushforwardFromOpen V ≅
        modulePushforwardFromOpen U ⋙ RingedSpace.Hom.pushforward f :=
    (SheafOfModules.pushforwardComp
        (RingedSpace.Hom.toRingCatSheafHom iV)
        (RingedSpace.Hom.toRingCatSheafHom g)) ≪≫
      hpush ≪≫
      (SheafOfModules.pushforwardComp
        (RingedSpace.Hom.toRingCatSheafHom f)
        (RingedSpace.Hom.toRingCatSheafHom iU)).symm
  -- Proof comment: this is the ambient pushforward comparison behind the eventual
  -- Beck-Chevalley isomorphism `(f_* ℱ)|_V ≅ g_*(ℱ|_U)`.
  Functor.isoWhiskerLeft (moduleRestrictionToOpen X U) compIso

/-- Helper for Lemma 20.32.4: the canonical open-pushforward route from `U` to `Y` agrees with
first pushing forward along `g : U ⟶ V` and then from `V` to `Y`. -/
noncomputable def modulePushforwardFromOpenAlong_restrictedIso :
    moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g ⋙ modulePushforwardFromOpen V ≅
      OpenSubspace.Pushforward.along f U :=
  -- Proof comment: expand `OpenSubspace.Pushforward.along` and reuse the
  -- structural postcomposition comparison just proved.
  restrictedPushforward_postcomposeOpenIso (f := f) (V := V)

/-- Helper for Lemma 20.32.4: after pushing forward from `V` back to `Y`, the restricted-open
comparison is already a functor isomorphism to the shared owner
`OpenSubspace.Pushforward.along f U`. -/
theorem modulePushforwardFromOpenAlong_restricted_isomorphic :
    IsIsomorphic
      (moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g ⋙ modulePushforwardFromOpen V)
      (OpenSubspace.Pushforward.along f U) := by
  -- Proof comment: package the canonical isomorphism above as an `IsIsomorphic` witness so the
  -- later derived proof can reuse it without reopening the structural comparison.
  exact ⟨modulePushforwardFromOpenAlong_restrictedIso (f := f) (V := V)⟩

/-- Helper for Lemma 20.32.4: the postcomposition comparison can be used objectwise without
reopening the functor-level structural proof. -/
noncomputable def restrictedPushforward_postcomposeOpen_appIso
    (ℱ : RingedSpace.Modules X) :
    ((moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g ⋙ modulePushforwardFromOpen V).obj
      ℱ) ≅
      ((OpenSubspace.Pushforward.along f U).obj ℱ) :=
  (restrictedPushforward_postcomposeOpenIso (f := f) (V := V)).app ℱ

/-- Helper for Lemma 20.32.4: the objectwise postcomposition comparison is already an
isomorphism of module sheaves. -/
theorem restrictedPushforward_postcomposeOpen_app_isomorphic
    (ℱ : RingedSpace.Modules X) :
    IsIsomorphic
      ((moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g ⋙
        modulePushforwardFromOpen V).obj ℱ)
      ((OpenSubspace.Pushforward.along f U).obj ℱ) := by
  -- Proof comment: this is the objectwise form of the structural postcomposition isomorphism,
  -- packaged for later use without reopening the functor-level iso.
  exact ⟨restrictedPushforward_postcomposeOpen_appIso (f := f) (V := V) ℱ⟩

/-- Helper for Lemma 20.32.4: after postcomposing by the ambient open pushforward from `V` back
to `Y`, the right-hand restricted-open functor is already the shared owner
`OpenSubspace.Pushforward.along f U`. -/
theorem modulePushforward_restrict_target_postcompose_isomorphic :
    IsIsomorphic
      ((moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g) ⋙
        modulePushforwardFromOpen V)
      (OpenSubspace.Pushforward.along f U) := by
  -- Proof comment: this is exactly the structural postcomposition comparison proved above, now
  -- packaged on the explicit functor surface that the remaining Beck-Chevalley blocker needs.
  exact ⟨restrictedPushforward_postcomposeOpenIso (f := f) (V := V)⟩

/-- Helper for Lemma 20.32.4: the restricted square commutes on the opens-site functors. -/
theorem opensRingedSiteHom_restrictedSquare_comm :
    (opensRingedSiteHom (Y.ofRestrict V.isOpenEmbedding)).base ⋙
        (opensRingedSiteHom g).base =
      (opensRingedSiteHom f).base ⋙
      (opensRingedSiteHom
          (X.ofRestrict (preimageOpen f V).isOpenEmbedding)).base := sorry

/-- Helper for Lemma 20.32.4: the restricted-open square also commutes as a strict equality of
opens-site ringed-space morphisms, so the transported structure-sheaf map disappears after
normalization. -/
theorem opensRingedSiteHom_restrictedSquare_eq :
    opensRingedSiteHom g ≫
        opensRingedSiteHom (Y.ofRestrict V.isOpenEmbedding) =
      opensRingedSiteHom (X.ofRestrict (preimageOpen f V).isOpenEmbedding) ≫
        opensRingedSiteHom f := sorry

/-- Helper for Lemma 20.32.4: the remaining underived gap is the Beck-Chevalley comparison
`(f_* ℱ)|_V ≅ g_*(ℱ|_U)` packaged as a natural isomorphism. -/
noncomputable def modulePushforward_restrictToOpenIso :
    RingedSpace.Hom.pushforward f ⋙ moduleRestrictionToOpen Y V ≅
      moduleRestrictionToOpen X U ⋙ RingedSpace.Hom.pushforward g :=
  OpenSubspace.BaseChange.baseChangeIso f V

-- Proof sketch: represent `E` by a K-injective complex `I`. By Lemma `20.32.1`, the restriction
-- `I|_{f^{-1}(V)}` is again K-injective, so `R(f)_* E` and `R(g)_*(E|_{f^{-1}(V)})` are
-- computed by
-- the underived pushforwards of these representatives. The ordinary sheaf identity
-- `(f_* ℱ)|_V = g_*(ℱ|_{f^{-1}(V)})` then yields the functor-level comparison,
-- whose source-facing objectwise specialization is the Stacks statement below.
/-- Functor-level companion to Lemma 20.32.4: restricting `R(f)_*` to `V` is canonically
isomorphic to first restricting to `U = f^{-1}(V)` and then applying the derived pushforward
along `g : U ⟶ V`. -/
theorem moduleDerivedPushforward_restrict_isomorphic :
    IsIsomorphic (R(f)_* ⋙ DResY) (DResX ⋙ R(g)_*) := by
  -- Route correction: the next stable route is the `Lemma_21_20_4` pattern. First normalize the
  -- underived Beck-Chevalley isomorphism on cochain complexes, then lift it with
  -- `Functor.rightDerivedNatIso`.
  -- TODO: once `modulePushforward_restrictToOpenIso` is available on the explicit owner surface,
  -- define the source and target right-derived units and apply `Functor.rightDerivedNatIso`.
  sorry

/-- Lemma 20.32.4: for `E : D(𝒪_X)`, the restriction of `R(f)_* E` to `V` is canonically
isomorphic to `Rg_*(E|_U)`, where `U = f^{-1}(V)` and `g : U ⟶ V` is the induced morphism. -/
@[stacks 08FE]
theorem moduleDerivedPushforward_restrict_obj_isomorphic
    (E : DModX) : IsIsomorphic (((R(f)_*).obj E) ↾[V]) ((R(g)_*).obj (E ↾[U])) := by
  rcases moduleDerivedPushforward_restrict_isomorphic f V with ⟨e⟩
  let eSource := OpenSubspace.Restriction.derivedObjIsoRestricted Y V ((R(f)_*).obj E)
  let eTarget := OpenSubspace.Restriction.derivedObjIsoRestricted X U E
  exact ⟨eSource.symm ≪≫ e.app E ≪≫ (R(g)_*).mapIso eTarget⟩

end

end AlgebraicGeometry.RingedSpace
