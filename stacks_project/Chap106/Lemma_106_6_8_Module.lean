/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.CategoryTheory.Fibered.Gerbe.Band
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap106.Lemma_106_6_8_Inertia

/-!
# Band of the gerbe of first-order lifts as an O_W-module

The sheaf of groups G of Lemma 8.11.8 for the gerbe of lifts of Remark 106.6.1
is a band. The first-order Hom-parameter modules of lifts determine a
quasi-coherent O_W-module structure on any such band, recovered after forgetting
to W_spaces,étale and after pullback along each lift. The Hom-parameter
pullback is the 0CKH identification with autSheaf, compared with the band
comparison to additive automorphism sheaves, rather than an arbitrary module iso.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicSpace
open Functor.IsFibered.InGroupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}}

/-- The underlying additive sheaf of an `O_W`-module on the universe-lifted small
étale ringed site. -/
def toAddCommSheaf {W : AlgebraicSpace S}
    (M : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)) :
    Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (commRingedSiteLift W).structureSheaf).obj M

/-- `toAddCommSheaf M` is the forgetful additive sheaf of `M`. -/
theorem toAddCommSheaf_eq {W : AlgebraicSpace S}
    (M : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)) :
    toAddCommSheaf M =
      (SheafOfModules.toSheaf (commRingedSiteLift W).structureSheaf).obj M :=
  rfl

/-- An isomorphism of `O_W`-modules induces an isomorphism of underlying additive
sheaves. -/
def toAddCommSheafMapIso {W : AlgebraicSpace S}
    {M N : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)} (e : M ≅ N) :
    toAddCommSheaf M ≅ toAddCommSheaf N :=
  (SheafOfModules.toSheaf (commRingedSiteLift W).structureSheaf).mapIso e

/-- Cocontinuous extension of a small-étale additive sheaf on `W` to
`W_spaces,étale`. -/
def toSpacesAddCommSheaf {W : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1} :=
  ((smallEtaleInclusion W).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology W) (spacesEtaleTopology W)).obj F

/-- `toSpacesAddCommSheaf F` is cocontinuous extension along `smallEtaleInclusion`. -/
theorem toSpacesAddCommSheaf_eq {W : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    toSpacesAddCommSheaf F =
      ((smallEtaleInclusion W).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology W) (spacesEtaleTopology W)).obj F :=
  rfl

/-- An isomorphism of small-étale additive sheaves extends to `W_spaces,étale`. -/
def toSpacesAddCommSheafMapIso {W : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}} (e : F ≅ G) :
    toSpacesAddCommSheaf F ≅ toSpacesAddCommSheaf G :=
  ((smallEtaleInclusion W).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology W) (spacesEtaleTopology W)).mapIso e

/-- Identity-on-sections comparison `O_U ⟶ a_small⁻¹ O_W` for an étale morphism
`a : U ⟶ W`, at the universe-lifted commutative structure sheaf. -/
def pullbackStructureMap {U W : AlgebraicSpace S} (a : U ⟶ W) [AlgebraicSpace.Etale a] :
    (commRingedSiteLift U).structureSheaf ⟶
      ((Modules.restrictPostcompose a).sheafPushforwardContinuous RingCat.{u + 1}
        (smallEtaleTopology U) (smallEtaleTopology W)).obj
        (commRingedSiteLift W).structureSheaf :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- `pullbackStructureMap a` is the identity on sections. -/
theorem pullbackStructureMap_app {U W : AlgebraicSpace S} (a : U ⟶ W) [AlgebraicSpace.Etale a]
    (V : (smallEtaleSite U)ᵒᵖ) :
    (pullbackStructureMap a).hom.app V = 𝟙 _ :=
  rfl

/-- Pullback of universe-lifted `O_W`-modules along an étale morphism `a : U ⟶ W`. -/
def pullbackModule {U W : AlgebraicSpace S} (a : U ⟶ W) [AlgebraicSpace.Etale a] :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W) ⥤
      RingedSite.ModuleCat.{u + 1} (commRingedSiteLift U) :=
  SheafOfModules.pushforward.{u + 1} (pullbackStructureMap a)

/-- `pullbackModule a` is module pushforward along `pullbackStructureMap a`. -/
theorem pullbackModule_eq {U W : AlgebraicSpace S} (a : U ⟶ W) [AlgebraicSpace.Etale a] :
    pullbackModule a = SheafOfModules.pushforward.{u + 1} (pullbackStructureMap a) :=
  rfl

variable {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable (iX : X ⟶ X') [IsThickening iX]
variable {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
variable [Groupoids.Hom.Smooth x]

/-- A quasi-coherent `O_W`-module structure on a band `G` of the gerbe of lifts,
with named comparison to `G` after forgetting to `W_spaces,étale` and named
pullback comparison to the Hom-parameter module of every lift. The Hom-parameter
pullback is intended to be the 0CKH identification with `autSheaf`, compared
along `IsBand.comparison` with the additive automorphism sheaf, rather than an
arbitrary module isomorphism; that commuting triangle is not yet named. -/
structure IsBandModule [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G)
    (M : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)) where
  /-- The module is quasi-coherent. -/
  isQuasicoherent : M.IsQuasicoherent
  /-- Extending the underlying additive sheaf of `M` to `W_spaces,étale` recovers
  `G`. -/
  underlyingIso : toSpacesAddCommSheaf (toAddCommSheaf M) ≅ G
  /-- Pullback of `M` along the étale structure map of a lift is the
  Hom-parameter module of that lift. -/
  pullbackIso : ∀ ξ : Object iX x,
    (pullbackModule ξ.a).obj M ≅ Object.parameterModule iX x ξ

/-- Package quasi-coherence and the named comparisons as a band-module
structure on `M`. -/
def IsBandModule.ofComparisons [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    {G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}}
    {hG : IsBand (p iX x) (spacesEtaleTopology W) G}
    {M : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)}
    (isQuasicoherent : M.IsQuasicoherent)
    (underlyingIso : toSpacesAddCommSheaf (toAddCommSheaf M) ≅ G)
    (pullbackIso : ∀ ξ : Object iX x,
      (pullbackModule ξ.a).obj M ≅ Object.parameterModule iX x ξ) :
    IsBandModule iX x G hG M :=
  ⟨isQuasicoherent, underlyingIso, pullbackIso⟩

/-- An isomorphism of candidate band modules is compatible when it identifies the
named underlying and pullback comparisons. -/
def CompatibleModuleIso [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    {G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}}
    {hG : IsBand (p iX x) (spacesEtaleTopology W) G}
    {M N : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)}
    (hM : IsBandModule iX x G hG M) (hN : IsBandModule iX x G hG N)
    (e : M ≅ N) : Prop :=
  toSpacesAddCommSheafMapIso (toAddCommSheafMapIso e) ≪≫ hN.underlyingIso =
      hM.underlyingIso ∧
    ∀ ξ : Object iX x,
      hM.pullbackIso ξ = (pullbackModule ξ.a).mapIso e ≪≫ hN.pullbackIso ξ

/-- Compatibility of a module isomorphism is the pair of underlying and
pullback comparison identities. -/
theorem compatibleModuleIso_iff [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    {G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}}
    {hG : IsBand (p iX x) (spacesEtaleTopology W) G}
    {M N : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W)}
    (hM : IsBandModule iX x G hG M) (hN : IsBandModule iX x G hG N)
    (e : M ≅ N) :
    CompatibleModuleIso iX x hM hN e ↔
      toSpacesAddCommSheafMapIso (toAddCommSheafMapIso e) ≪≫ hN.underlyingIso =
          hM.underlyingIso ∧
        ∀ ξ : Object iX x,
          hM.pullbackIso ξ = (pullbackModule ξ.a).mapIso e ≪≫ hN.pullbackIso ξ :=
  sorry

/-- Existence of a quasi-coherent `O_W`-module structure on a band of the gerbe
of first-order lifts. -/
theorem exists_bandModule [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) :
    Nonempty
      (Σ M : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W),
        IsBandModule iX x G hG M) :=
  sorry

/-- Selected quasi-coherent module structure on a band, together with its
comparisons. Consumers should use `bandModule` and `bandModule_spec`. -/
def bandModuleWitness [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) :
    Σ M : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W),
      IsBandModule iX x G hG M :=
  Classical.choice (exists_bandModule iX x G hG)

/-- The sheaf of groups `G` of Lemma 8.11.8, as a quasi-coherent `O_W`-module on
the universe-lifted small étale site of `W`. -/
def bandModule [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W) :=
  (bandModuleWitness iX x G hG).1

/-- `bandModule G hG` carries the quasi-coherent comparisons to `G` and to
the Hom-parameter module of every lift. -/
def bandModule_spec [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) :
    IsBandModule iX x G hG (bandModule iX x G hG) :=
  (bandModuleWitness iX x G hG).2

/-- Extending the underlying additive sheaf of `bandModule G hG` to
`W_spaces,étale` recovers `G`. -/
def bandModule_underlyingIso [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) :
    toSpacesAddCommSheaf (toAddCommSheaf (bandModule iX x G hG)) ≅ G :=
  (bandModule_spec iX x G hG).underlyingIso

/-- Pullback of `bandModule G hG` along a lift is the Hom-parameter module of
that lift. -/
def bandModule_pullbackIso [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) (ξ : Object iX x) :
    (pullbackModule ξ.a).obj (bandModule iX x G hG) ≅
      Object.parameterModule iX x ξ :=
  (bandModule_spec iX x G hG).pullbackIso ξ

/-- `bandModule G hG` is quasi-coherent. -/
instance instBandModuleIsQuasicoherent [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) :
    (bandModule iX x G hG).IsQuasicoherent :=
  sorry

/-- Over a lift `ξ`, the band is identified with the additive automorphism sheaf
of `ξ`. -/
def bandModule_overIso [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)]
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (spacesEtaleTopology W) G) (ξ : Object iX x) :
    G.over ξ.toSpacesEtale ≅
      Automorphism.addComm.sheaf (p iX x) (spacesEtaleTopology W) ⟨ξ, rfl⟩ :=
  (IsBand.comparison hG).iso ⟨ξ, rfl⟩

/-- The convenient selected band of the gerbe of first-order lifts. -/
def bandSheaf [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)] :
    Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1} :=
  (IsGerbe.bandChoice :
      Band.Choice (p iX x) (spacesEtaleTopology W)).sheaf

/-- `bandSheaf` is the additive sheaf of the selected band of Lemma 8.11.8. -/
theorem bandSheaf_eq [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)] :
    bandSheaf iX x =
      (IsGerbe.bandChoice :
          Band.Choice (p iX x) (spacesEtaleTopology W)).sheaf :=
  rfl

/-- The selected band of the gerbe of lifts satisfies the band predicate. -/
theorem bandSheaf_isBand [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)] :
    IsBand (p iX x) (spacesEtaleTopology W) (bandSheaf iX x) :=
  sorry

/-- The quasi-coherent `O_W`-module structure on the selected band of
Lemma 8.11.8. -/
def bandChoiceModule [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)] :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W) :=
  bandModule iX x (bandSheaf iX x) (bandSheaf_isBand iX x)

/-- `bandChoiceModule` is `bandModule` of the selected band. -/
theorem bandChoiceModule_eq [IsFirstOrderThickening iX]
    [Automorphism.IsAbelian (p iX x)] :
    bandChoiceModule iX x =
      bandModule iX x (bandSheaf iX x) (bandSheaf_isBand iX x) :=
  rfl

end AlgebraicGeometry.AlgebraicStack.Lift
