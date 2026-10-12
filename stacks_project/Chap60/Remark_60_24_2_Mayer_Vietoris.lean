/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_1_Higher_direct_images_Context
public import stacks_project.Chap60.Lemma_60_9_5_Functor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline
open TopologicalSpace

noncomputable section

universe z u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Source PD thickening scheme of the higher-direct-image setup. -/
abbrev sourceThickening (c : HigherDirectImageContext.{u}) : Scheme.{u} :=
  c.S.scheme

/-- Source PD ideal sheaf of the higher-direct-image setup. -/
abbrev sourceIdeal (c : HigherDirectImageContext.{u}) :
    (sourceThickening c).IdealSheafData :=
  c.S.ideal

/-- Closed fibre of the source PD thickening. -/
abbrev sourceZeroFiber (c : HigherDirectImageContext.{u}) : Scheme.{u} :=
  (sourceIdeal c).subscheme

/-- Closed-fibre closed immersion of the source PD thickening. -/
abbrev sourceZeroFiberι (c : HigherDirectImageContext.{u}) :
    sourceZeroFiber c ⟶ sourceThickening c :=
  (sourceIdeal c).subschemeι

/-- Affine opens of the source PD thickening. -/
abbrev sourceAffineOpens (c : HigherDirectImageContext.{u}) :=
  (sourceThickening c).affineOpens

/-- The small crystalline ringed site of the source scheme in Remark 60.24.1. -/
abbrev crystallineSourceSite (c : HigherDirectImageContext.{u}) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf
    (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
      c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X

/-- The small crystalline ringed site of the target scheme in Remark 60.24.1. -/
abbrev crystallineTargetSite (c : HigherDirectImageContext.{u}) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf
    (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
      c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y

/-- Compatibility of the identity map on the closed fibre of the source PD thickening. -/
theorem crystallineOpen_id_zeroFiber_comm (c : HigherDirectImageContext.{u}) :
    (𝟙 (sourceZeroFiber c)) ≫ sourceZeroFiberι c =
      sourceZeroFiberι c ≫ 𝟙 (sourceThickening c) := sorry

/-- Compatibility of the identity map with the structure morphism to `Spec ℤ_(p)`. -/
theorem crystallineOpen_id_base_over (c : HigherDirectImageContext.{u}) :
    (𝟙 (sourceThickening c)) ≫ c.s = c.s := sorry

/-- The identity map of the source thickening is compatible with the PD ideal. -/
theorem crystallineOpen_id_ideal_compatible (c : HigherDirectImageContext.{u}) :
    (sourceIdeal c).comap (𝟙 (sourceThickening c)) ≤ sourceIdeal c := sorry

/-- Identity divided-power setup morphism of the source PD thickening in Remark 60.24.1. -/
noncomputable def crystallineOpen_idDividedPowerHom
    (c : HigherDirectImageContext.{u}) :
    DividedPowerSchemeHom (sourceIdeal c) (sourceIdeal c) c.s c.s :=
  DividedPowerSchemeHom.of (𝟙 (sourceThickening c)) (𝟙 (sourceZeroFiber c))
    (crystallineOpen_id_zeroFiber_comm c)
    (crystallineOpen_id_base_over c)
    (crystallineOpen_id_ideal_compatible c)

/-- Local nilpotence of `p` pulls back from `c.Xsch` to an open subscheme. -/
theorem crystallineOpen_pNilpotent
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch) :
    ∀ V : U.toScheme.affineOpens, IsNilpotent (c.p : Γ(U.toScheme, V)) := sorry

/-- Identity morphism of the source PD thickening. -/
abbrev crystallineOpen_idSchemeHom (c : HigherDirectImageContext.{u}) :
    sourceThickening c ⟶ sourceThickening c := 𝟙 _

/-- Identity PD morphisms preserve divided powers on affine opens of the source thickening. -/
theorem crystallineOpen_id_dividedPowers
    (c : HigherDirectImageContext.{u}) :
    ∀ (V : sourceAffineOpens c) (W : sourceAffineOpens c)
      (hVW : W.1 ≤ (crystallineOpen_idSchemeHom c) ⁻¹ᵁ V.1),
      (c.S.dividedPowers V).IsDPMorphism (c.S.dividedPowers W)
        ((crystallineOpen_idSchemeHom c).appLE V W hVW).hom := sorry

/-- Closed-fibre compatibility for the open immersion `U.ι` over the identity PD morphism. -/
theorem crystallineOpen_h_comm
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch) :
    U.ι ≫ c.x₀ =
      (U.ι ≫ c.x₀) ≫ (crystallineOpen_idDividedPowerHom c).zeroFiberMap := sorry

/-- Closed-fibre compatibility for a nested open immersion `W ≤ U`. -/
theorem crystallineOpen_h_comm_le
    (c : HigherDirectImageContext.{u}) {W U : Opens c.Xsch} (h : W ≤ U) :
    c.Xsch.homOfLE h ≫ (U.ι ≫ c.x₀) =
      (W.ι ≫ c.x₀) ≫ (crystallineOpen_idDividedPowerHom c).zeroFiberMap := sorry

/-- Open restriction functor `Cris(U/S) ⥤ Cris(X/S)` on small crystalline sites. -/
noncomputable def crystallineOpenSmallFunctor
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch) :
    smallCrystallineSite (sourceThickening c) (sourceIdeal c) c.S.dividedPowers c.S.compatible
        U.toScheme (U.ι ≫ c.x₀) ⥤
      smallCrystallineSite (sourceThickening c) (sourceIdeal c) c.S.dividedPowers c.S.compatible
        c.Xsch c.x₀ :=
  openCrystallineSmallFunctor U.ι (sourceIdeal c) (sourceIdeal c)
    c.S.dividedPowers c.S.dividedPowers c.S.compatible c.S.compatible
    c.s c.s c.x₀ (U.ι ≫ c.x₀) c.pX (crystallineOpen_pNilpotent c U)
    (crystallineOpen_idDividedPowerHom c) (crystallineOpen_h_comm c U)
    (crystallineOpen_id_dividedPowers c)

/-- The open restriction functor is the open-immersion functor of Lemma 60.9.5. -/
theorem crystallineOpenSmallFunctor_eq
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch) :
    crystallineOpenSmallFunctor c U =
      openCrystallineSmallFunctor U.ι (sourceIdeal c) (sourceIdeal c)
        c.S.dividedPowers c.S.dividedPowers c.S.compatible c.S.compatible
        c.s c.s c.x₀ (U.ι ≫ c.x₀) c.pX (crystallineOpen_pNilpotent c U)
        (crystallineOpen_idDividedPowerHom c) (crystallineOpen_h_comm c U)
        (crystallineOpen_id_dividedPowers c) := sorry

/-- Structure sheaf of `Cris(U/S)` obtained as inverse image of `c.𝒪X` along the
right adjoint of `crystallineOpenSmallFunctor`. -/
noncomputable def crystallineOpenStructureSheaf
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint] :
    Sheaf (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
      c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
      (crystallineOpen_pNilpotent c U)) RingCat.{u} :=
  ((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPullback RingCat.{u}
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))).obj c.𝒪X

/-- The restricted structure sheaf is inverse image of `c.𝒪X` along the open-inclusion right adjoint. -/
theorem crystallineOpenStructureSheaf_eq
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint] :
    crystallineOpenStructureSheaf c U =
      ((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPullback RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).obj c.𝒪X := sorry

/-- The small crystalline ringed site of an open of the source scheme over the same PD base. -/
noncomputable abbrev crystallineOpenSourceSite
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint] :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf
    (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
      c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
      (crystallineOpen_pNilpotent c U))
    (crystallineOpenStructureSheaf c U)

/-- The open crystalline site is the small crystalline ringed site of `U.toScheme`. -/
theorem crystallineOpenSourceSite_eq
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint] :
    crystallineOpenSourceSite c U =
      RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))
        (crystallineOpenStructureSheaf c U) := sorry

/-- Nested open restriction `Cris(W/S) ⥤ Cris(U/S)` for `W ≤ U`. -/
noncomputable def crystallineOpenSmallFunctor_le
    (c : HigherDirectImageContext.{u}) {W U : Opens c.Xsch} (h : W ≤ U) :
    smallCrystallineSite (sourceThickening c) (sourceIdeal c) c.S.dividedPowers c.S.compatible
        W.toScheme (W.ι ≫ c.x₀) ⥤
      smallCrystallineSite (sourceThickening c) (sourceIdeal c) c.S.dividedPowers c.S.compatible
        U.toScheme (U.ι ≫ c.x₀) :=
  openCrystallineSmallFunctor (c.Xsch.homOfLE h) (sourceIdeal c) (sourceIdeal c)
    c.S.dividedPowers c.S.dividedPowers c.S.compatible c.S.compatible
    c.s c.s (U.ι ≫ c.x₀) (W.ι ≫ c.x₀)
    (crystallineOpen_pNilpotent c U) (crystallineOpen_pNilpotent c W)
    (crystallineOpen_idDividedPowerHom c) (crystallineOpen_h_comm_le c h)
    (crystallineOpen_id_dividedPowers c)

/-- The nested open functor is the open-immersion functor of Lemma 60.9.5. -/
theorem crystallineOpenSmallFunctor_le_eq
    (c : HigherDirectImageContext.{u}) {W U : Opens c.Xsch} (h : W ≤ U) :
    crystallineOpenSmallFunctor_le c h =
      openCrystallineSmallFunctor (c.Xsch.homOfLE h) (sourceIdeal c) (sourceIdeal c)
        c.S.dividedPowers c.S.dividedPowers c.S.compatible c.S.compatible
        c.s c.s (U.ι ≫ c.x₀) (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U) (crystallineOpen_pNilpotent c W)
        (crystallineOpen_idDividedPowerHom c) (crystallineOpen_h_comm_le c h)
        (crystallineOpen_id_dividedPowers c) := sorry

/-- The first displayed map of the relative crystalline Mayer–Vietoris triangle:
the biproduct of the two derived restriction units of `Rf_cris,*`. -/
noncomputable abbrev crystallinePushforward_mayerVietoris_toBiprod
    {X Y XU XV : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y) (fU : RingedSite.Hom XU Y) (fV : RingedSite.Hom XV Y)
    [UnivLE.{u + 1, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fV) (ModuleQis.{z} XV)]
    {F : ModuleDerived.{z} X}
    {FU : ModuleDerived.{z} XU} {FV : ModuleDerived.{z} XV}
    (resU : (modulePushforwardDerived.{z} f).obj F ⟶
      (modulePushforwardDerived.{z} fU).obj FU)
    (resV : (modulePushforwardDerived.{z} f).obj F ⟶
      (modulePushforwardDerived.{z} fV).obj FV) :
    (modulePushforwardDerived.{z} f).obj F ⟶
      (modulePushforwardDerived.{z} fU).obj FU ⊞
        (modulePushforwardDerived.{z} fV).obj FV :=
  biprod.lift resU resV

/-- Unfolding of the Mayer–Vietoris restriction-to-biproduct map. -/
theorem crystallinePushforward_mayerVietoris_toBiprod_apply
    {X Y XU XV : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y) (fU : RingedSite.Hom XU Y) (fV : RingedSite.Hom XV Y)
    [UnivLE.{u + 1, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fV) (ModuleQis.{z} XV)]
    {F : ModuleDerived.{z} X}
    {FU : ModuleDerived.{z} XU} {FV : ModuleDerived.{z} XV}
    (resU : (modulePushforwardDerived.{z} f).obj F ⟶
      (modulePushforwardDerived.{z} fU).obj FU)
    (resV : (modulePushforwardDerived.{z} f).obj F ⟶
      (modulePushforwardDerived.{z} fV).obj FV) :
    crystallinePushforward_mayerVietoris_toBiprod f fU fV resU resV =
      biprod.lift resU resV := sorry

/-- The second displayed map of the relative crystalline Mayer–Vietoris triangle:
the overlap-difference of the two restrictions to `X' ∩ X''`. -/
noncomputable abbrev crystallinePushforward_mayerVietoris_difference
    {Y XU XV XW : RingedSite.{u + 1, u, u}}
    (fU : RingedSite.Hom XU Y) (fV : RingedSite.Hom XV Y) (fW : RingedSite.Hom XW Y)
    [UnivLE.{u + 1, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fV) (ModuleQis.{z} XV)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fW) (ModuleQis.{z} XW)]
    {FU : ModuleDerived.{z} XU} {FV : ModuleDerived.{z} XV}
    {FW : ModuleDerived.{z} XW}
    (resUW : (modulePushforwardDerived.{z} fU).obj FU ⟶
      (modulePushforwardDerived.{z} fW).obj FW)
    (resVW : (modulePushforwardDerived.{z} fV).obj FV ⟶
      (modulePushforwardDerived.{z} fW).obj FW) :
    (modulePushforwardDerived.{z} fU).obj FU ⊞
        (modulePushforwardDerived.{z} fV).obj FV ⟶
      (modulePushforwardDerived.{z} fW).obj FW :=
  biprod.desc resUW (-resVW)

/-- Unfolding of the Mayer–Vietoris overlap-difference map. -/
theorem crystallinePushforward_mayerVietoris_difference_apply
    {Y XU XV XW : RingedSite.{u + 1, u, u}}
    (fU : RingedSite.Hom XU Y) (fV : RingedSite.Hom XV Y) (fW : RingedSite.Hom XW Y)
    [UnivLE.{u + 1, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fV) (ModuleQis.{z} XV)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} fW) (ModuleQis.{z} XW)]
    {FU : ModuleDerived.{z} XU} {FV : ModuleDerived.{z} XV}
    {FW : ModuleDerived.{z} XW}
    (resUW : (modulePushforwardDerived.{z} fU).obj FU ⟶
      (modulePushforwardDerived.{z} fW).obj FW)
    (resVW : (modulePushforwardDerived.{z} fV).obj FV ⟶
      (modulePushforwardDerived.{z} fW).obj FW) :
    crystallinePushforward_mayerVietoris_difference fU fV fW resUW resVW =
      biprod.desc resUW (-resVW) := sorry

/-- Open inclusion of small crystalline ringed sites associated to
`crystallineOpenSmallFunctor`. The base functor is the right adjoint of the
open-immersion functor of Lemma 60.9.5, and the structure-sheaf map is the
unit of `sheafAdjunctionContinuous`. -/
noncomputable def crystallineOpenInclusion
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint] :
    RingedSite.Hom (crystallineOpenSourceSite c U) (crystallineSourceSite c) where
  base := (crystallineOpenSmallFunctor c U).rightAdjoint
  structureSheafMap :=
    ((crystallineOpenSmallFunctor c U).rightAdjoint.sheafAdjunctionContinuous RingCat.{u}
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))).unit.app c.𝒪X

/-- The open inclusion has the right adjoint of `crystallineOpenSmallFunctor` as base functor. -/
theorem crystallineOpenInclusion_base
    (c : HigherDirectImageContext.{u}) (U : Opens c.Xsch)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint] :
    (crystallineOpenInclusion c U).base =
      (crystallineOpenSmallFunctor c U).rightAdjoint := sorry

/-- Nested inverse image of `𝒪_U` recovers the structure sheaf of `Cris(W/S)`. -/
theorem crystallineOpenStructureSheaf_le_pullback
    (c : HigherDirectImageContext.{u}) {W U : Opens c.Xsch} (h : W ≤ U)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [Functor.IsContinuous (crystallineOpenSmallFunctor c W)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [(crystallineOpenSmallFunctor c W).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (crystallineOpenSmallFunctor c W).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint]
    [((crystallineOpenSmallFunctor c W).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c W))).IsRightAdjoint]
    [Functor.IsContinuous (crystallineOpenSmallFunctor_le c h)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))]
    [(crystallineOpenSmallFunctor_le c h).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (crystallineOpenSmallFunctor_le c h).rightAdjoint]
    [((crystallineOpenSmallFunctor_le c h).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c W))).IsRightAdjoint] :
    ((crystallineOpenSmallFunctor_le c h).rightAdjoint.sheafPullback RingCat.{u}
        (crystallineOpenSourceSite c U).siteTopology
        (crystallineOpenSourceSite c W).siteTopology).obj
      (crystallineOpenSourceSite c U).structureSheaf =
      (crystallineOpenSourceSite c W).structureSheaf := sorry

/-- Nested open inclusion `Cris(W/S) ⟶ Cris(U/S)` associated to `W ≤ U`. -/
noncomputable def crystallineOpenInclusion_le
    (c : HigherDirectImageContext.{u}) {W U : Opens c.Xsch} (h : W ≤ U)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [Functor.IsContinuous (crystallineOpenSmallFunctor c W)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [(crystallineOpenSmallFunctor c W).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (crystallineOpenSmallFunctor c W).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint]
    [((crystallineOpenSmallFunctor c W).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c W))).IsRightAdjoint]
    [Functor.IsContinuous (crystallineOpenSmallFunctor_le c h)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))]
    [(crystallineOpenSmallFunctor_le c h).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (crystallineOpenSmallFunctor_le c h).rightAdjoint]
    [((crystallineOpenSmallFunctor_le c h).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c W))).IsRightAdjoint] :
    RingedSite.Hom (crystallineOpenSourceSite c W) (crystallineOpenSourceSite c U) where
  base := (crystallineOpenSmallFunctor_le c h).rightAdjoint
  structureSheafMap :=
    ((crystallineOpenSmallFunctor_le c h).rightAdjoint.sheafAdjunctionContinuous RingCat.{u}
        (crystallineOpenSourceSite c U).siteTopology
        (crystallineOpenSourceSite c W).siteTopology).unit.app
      (crystallineOpenSourceSite c U).structureSheaf ≫
      ((crystallineOpenSmallFunctor_le c h).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (crystallineOpenSourceSite c U).siteTopology
        (crystallineOpenSourceSite c W).siteTopology).map
        (eqToHom (crystallineOpenStructureSheaf_le_pullback c h))

/-- Nested open inclusion has the right adjoint of `crystallineOpenSmallFunctor_le` as base. -/
theorem crystallineOpenInclusion_le_base
    (c : HigherDirectImageContext.{u}) {W U : Opens c.Xsch} (h : W ≤ U)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [Functor.IsContinuous (crystallineOpenSmallFunctor c W)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [(crystallineOpenSmallFunctor c W).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (crystallineOpenSmallFunctor c W).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint]
    [((crystallineOpenSmallFunctor c W).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c W))).IsRightAdjoint]
    [Functor.IsContinuous (crystallineOpenSmallFunctor_le c h)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))]
    [(crystallineOpenSmallFunctor_le c h).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c W))
      (crystallineOpenSmallFunctor_le c h).rightAdjoint]
    [((crystallineOpenSmallFunctor_le c h).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s W.toScheme (W.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c W))).IsRightAdjoint] :
    (crystallineOpenInclusion_le c h).base =
      (crystallineOpenSmallFunctor_le c h).rightAdjoint := sorry

/-- Restriction of a crystalline morphism along an open inclusion of small crystalline sites. -/
noncomputable abbrev crystallineRestrictedHom
    {XU X Y : RingedSite.{u + 1, u, u}}
    (j : RingedSite.Hom XU X) (f : RingedSite.Hom X Y) :
    RingedSite.Hom XU Y :=
  j.comp f

/-- Restricted crystalline morphisms are composition with the open inclusion. -/
theorem crystallineRestrictedHom_eq
    {XU X Y : RingedSite.{u + 1, u, u}}
    (j : RingedSite.Hom XU X) (f : RingedSite.Hom X Y) :
    crystallineRestrictedHom j f = j.comp f := sorry

/-- Restriction of a derived module along an open inclusion of small crystalline sites. -/
noncomputable abbrev crystallineRestrictedModule
    {XU X : RingedSite.{u + 1, u, u}} (j : RingedSite.Hom XU X)
    [UnivLE.{u + 1, z}]
    [(j.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} j) (ModuleQis.{z} X)]
    (F : ModuleDerived.{z} X) :
    ModuleDerived.{z} XU :=
  (modulePullbackDerived.{z} j).obj F

/-- Restricted derived modules are derived pullback along the open inclusion. -/
theorem crystallineRestrictedModule_eq
    {XU X : RingedSite.{u + 1, u, u}} (j : RingedSite.Hom XU X)
    [UnivLE.{u + 1, z}]
    [(j.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} j) (ModuleQis.{z} X)]
    (F : ModuleDerived.{z} X) :
    crystallineRestrictedModule.{z} j F = (modulePullbackDerived.{z} j).obj F := sorry

/-- The derived restriction unit of `Rf_*` along an open inclusion `j`, presented as
`Rf_*` of the derived adjunction unit `F ⟶ j_* L j^* F`. -/
noncomputable def crystallineDerivedRestrictionUnit
    {XU X Y : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y) (j : RingedSite.Hom XU X)
    [UnivLE.{u + 1, z}]
    [(j.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} j) (ModuleQis.{z} XU)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} j) (ModuleQis.{z} X)]
    [DerivedAdjunction.HasPair.{z} j]
    (F : ModuleDerived.{z} X) :
    (modulePushforwardDerived.{z} f).obj F ⟶
      (modulePushforwardDerived.{z} f).obj
        ((modulePushforwardDerived.{z} j).obj (crystallineRestrictedModule.{z} j F)) :=
  (modulePushforwardDerived.{z} f).map ((moduleDerivedAdjunction.{z} j).unit.app F)

/-- Unfolding of the derived restriction unit as `Rf_*` of the derived unit of `j`. -/
theorem crystallineDerivedRestrictionUnit_eq
    {XU X Y : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y) (j : RingedSite.Hom XU X)
    [UnivLE.{u + 1, z}]
    [(j.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} j) (ModuleQis.{z} XU)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} j) (ModuleQis.{z} X)]
    [DerivedAdjunction.HasPair.{z} j]
    (F : ModuleDerived.{z} X) :
    crystallineDerivedRestrictionUnit.{z} f j F =
      (modulePushforwardDerived.{z} f).map
        ((moduleDerivedAdjunction.{z} j).unit.app F) := sorry

/-- Overlap restriction of `RfU_* FU` along `W ≤ U`, after applying `Rf_*`. -/
noncomputable def crystallineDerivedOverlapRestriction
    {XW XU X Y : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y) (jU : RingedSite.Hom XU X) (jWU : RingedSite.Hom XW XU)
    [UnivLE.{u + 1, z}]
    [(jU.modulePushforward.{z}).IsRightAdjoint]
    [(jWU.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jWU) (ModuleQis.{z} XW)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jU) (ModuleQis.{z} X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jWU) (ModuleQis.{z} XU)]
    [DerivedAdjunction.HasPair.{z} jWU]
    (F : ModuleDerived.{z} X) :
    (modulePushforwardDerived.{z} f).obj
        ((modulePushforwardDerived.{z} jU).obj (crystallineRestrictedModule.{z} jU F)) ⟶
      (modulePushforwardDerived.{z} f).obj
        ((modulePushforwardDerived.{z} jU).obj
          ((modulePushforwardDerived.{z} jWU).obj
            (crystallineRestrictedModule.{z} jWU (crystallineRestrictedModule.{z} jU F)))) :=
  (modulePushforwardDerived.{z} f).map
    ((modulePushforwardDerived.{z} jU).map
      ((moduleDerivedAdjunction.{z} jWU).unit.app (crystallineRestrictedModule.{z} jU F)))

/-- Unfolding of the overlap restriction as `Rf_* jU_*` of the derived unit of `jWU`. -/
theorem crystallineDerivedOverlapRestriction_eq
    {XW XU X Y : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y) (jU : RingedSite.Hom XU X) (jWU : RingedSite.Hom XW XU)
    [UnivLE.{u + 1, z}]
    [(jU.modulePushforward.{z}).IsRightAdjoint]
    [(jWU.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jWU) (ModuleQis.{z} XW)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jU) (ModuleQis.{z} X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jWU) (ModuleQis.{z} XU)]
    [DerivedAdjunction.HasPair.{z} jWU]
    (F : ModuleDerived.{z} X) :
    crystallineDerivedOverlapRestriction.{z} f jU jWU F =
      (modulePushforwardDerived.{z} f).map
        ((modulePushforwardDerived.{z} jU).map
          ((moduleDerivedAdjunction.{z} jWU).unit.app
            (crystallineRestrictedModule.{z} jU F))) := sorry

/-- The two overlap presentations of `Rf_*` on `W = U ∩ V` agree. -/
theorem crystallineDerivedOverlapTarget_eq
    {XW XU XV X Y : RingedSite.{u + 1, u, u}}
    (f : RingedSite.Hom X Y)
    (jU : RingedSite.Hom XU X) (jV : RingedSite.Hom XV X)
    (jWU : RingedSite.Hom XW XU) (jWV : RingedSite.Hom XW XV)
    [UnivLE.{u + 1, z}]
    [(jU.modulePushforward.{z}).IsRightAdjoint]
    [(jV.modulePushforward.{z}).IsRightAdjoint]
    [(jWU.modulePushforward.{z}).IsRightAdjoint]
    [(jWV.modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jU) (ModuleQis.{z} XU)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jV) (ModuleQis.{z} XV)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jWU) (ModuleQis.{z} XW)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} jWV) (ModuleQis.{z} XW)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jU) (ModuleQis.{z} X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jV) (ModuleQis.{z} X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jWU) (ModuleQis.{z} XU)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{z} jWV) (ModuleQis.{z} XV)]
    (F : ModuleDerived.{z} X) :
    (modulePushforwardDerived.{z} f).obj
        ((modulePushforwardDerived.{z} jV).obj
          ((modulePushforwardDerived.{z} jWV).obj
            (crystallineRestrictedModule.{z} jWV (crystallineRestrictedModule.{z} jV F)))) =
      (modulePushforwardDerived.{z} f).obj
        ((modulePushforwardDerived.{z} jU).obj
          ((modulePushforwardDerived.{z} jWU).obj
            (crystallineRestrictedModule.{z} jWU
              (crystallineRestrictedModule.{z} jU F)))) := sorry

/-- Remark 60.24.2 (Mayer-Vietoris): in the standing setup of Remark 60.24.1, an
open covering `c.Xsch = U ∪ V` of the source scheme (not the target scheme
`c.X'sch` of 60.24.1) with overlap `W = U ∩ V` induces restricted crystalline
morphisms `fU = jU ≫ f`, `fV = jV ≫ f`, `fW = jW ≫ f` and restricted derived
modules `FU = L(jU)^* F`, `FV = L(jV)^* F`, `FW = L(jW)^* F`, where `jU`, `jV`,
`jW` are the open inclusions of small crystalline sites associated to
`crystallineOpenSmallFunctor`. There is a distinguished triangle
`Rf_cris,* F ⟶ RfU_cris,* FU ⊕ RfV_cris,* FV ⟶ RfW_cris,* FW ⟶ Rf_cris,* F[1]`
in `D(𝒪_{X'/S'})`, identified with `ModuleDerived` of the target crystalline
ringed site. The first two maps are the restriction-to-biproduct and
overlap-difference of the canonical `crystallineDerivedRestrictionUnit` maps;
the connecting map is existential. -/
@[stacks 07ML]
theorem crystallinePushforward_mayerVietoris_triangle
    (c : HigherDirectImageContext.{u})
    (U V : Opens c.Xsch) (hUV : U ⊔ V = ⊤)
    [Functor.IsContinuous (crystallineOpenSmallFunctor c U)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [Functor.IsContinuous (crystallineOpenSmallFunctor c V)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s V.toScheme (V.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c V))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [Functor.IsContinuous (crystallineOpenSmallFunctor c (U ⊓ V))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c (U ⊓ V)))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)]
    [(crystallineOpenSmallFunctor c U).IsLeftAdjoint]
    [(crystallineOpenSmallFunctor c V).IsLeftAdjoint]
    [(crystallineOpenSmallFunctor c (U ⊓ V)).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (crystallineOpenSmallFunctor c U).rightAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s V.toScheme (V.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c V))
      (crystallineOpenSmallFunctor c V).rightAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s c.Xsch c.x₀ c.pX)
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c (U ⊓ V)))
      (crystallineOpenSmallFunctor c (U ⊓ V)).rightAdjoint]
    [((crystallineOpenSmallFunctor c U).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))).IsRightAdjoint]
    [((crystallineOpenSmallFunctor c V).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s V.toScheme (V.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c V))).IsRightAdjoint]
    [((crystallineOpenSmallFunctor c (U ⊓ V)).rightAdjoint.sheafPushforwardContinuous RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX)
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c (U ⊓ V)))).IsRightAdjoint]
    [Functor.IsContinuous (crystallineOpenSmallFunctor_le c (inf_le_left : U ⊓ V ≤ U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c (U ⊓ V)))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))]
    [Functor.IsContinuous (crystallineOpenSmallFunctor_le c (inf_le_right : U ⊓ V ≤ V))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c (U ⊓ V)))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s V.toScheme (V.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c V))]
    [(crystallineOpenSmallFunctor_le c (inf_le_left : U ⊓ V ≤ U)).IsLeftAdjoint]
    [(crystallineOpenSmallFunctor_le c (inf_le_right : U ⊓ V ≤ V)).IsLeftAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c U))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c (U ⊓ V)))
      (crystallineOpenSmallFunctor_le c (inf_le_left : U ⊓ V ≤ U)).rightAdjoint]
    [IsMorphismOfSites
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s V.toScheme (V.ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c V))
      (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
        c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
        (crystallineOpen_pNilpotent c (U ⊓ V)))
      (crystallineOpenSmallFunctor_le c (inf_le_right : U ⊓ V ≤ V)).rightAdjoint]
    [((crystallineOpenSmallFunctor_le c (inf_le_left : U ⊓ V ≤ U)).rightAdjoint.sheafPushforwardContinuous
        RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s U.toScheme (U.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c U))
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c (U ⊓ V)))).IsRightAdjoint]
    [((crystallineOpenSmallFunctor_le c (inf_le_right : U ⊓ V ≤ V)).rightAdjoint.sheafPushforwardContinuous
        RingCat.{u}
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s V.toScheme (V.ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c V))
        (smallCrystallineTopology c.p (sourceThickening c) (sourceIdeal c) c.S.dividedPowers
          c.S.compatible c.s (U ⊓ V).toScheme ((U ⊓ V).ι ≫ c.x₀)
          (crystallineOpen_pNilpotent c (U ⊓ V)))).IsRightAdjoint]
    (f : RingedSite.Hom (crystallineSourceSite c) (crystallineTargetSite c))
    [UnivLE.{u + 1, z}]
    [((crystallineOpenInclusion c U).modulePushforward.{z}).IsRightAdjoint]
    [((crystallineOpenInclusion c V).modulePushforward.{z}).IsRightAdjoint]
    [((crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U)).modulePushforward.{z}).IsRightAdjoint]
    [((crystallineOpenInclusion_le c (inf_le_right : U ⊓ V ≤ V)).modulePushforward.{z}).IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} (crystallineSourceSite c))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (crystallineOpenInclusion c U))
      (ModuleQis.{z} (crystallineOpenSourceSite c U))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (crystallineOpenInclusion c V))
      (ModuleQis.{z} (crystallineOpenSourceSite c V))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U)))
      (ModuleQis.{z} (crystallineOpenSourceSite c (U ⊓ V)))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (crystallineOpenInclusion_le c (inf_le_right : U ⊓ V ≤ V)))
      (ModuleQis.{z} (crystallineOpenSourceSite c (U ⊓ V)))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} (crystallineOpenInclusion c U))
      (ModuleQis.{z} (crystallineSourceSite c))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} (crystallineOpenInclusion c V))
      (ModuleQis.{z} (crystallineSourceSite c))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U)))
      (ModuleQis.{z} (crystallineOpenSourceSite c U))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} (crystallineOpenInclusion_le c (inf_le_right : U ⊓ V ≤ V)))
      (ModuleQis.{z} (crystallineOpenSourceSite c V))]
    [DerivedAdjunction.HasPair.{z} (crystallineOpenInclusion c U)]
    [DerivedAdjunction.HasPair.{z} (crystallineOpenInclusion c V)]
    [DerivedAdjunction.HasPair.{z} (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U))]
    [DerivedAdjunction.HasPair.{z} (crystallineOpenInclusion_le c (inf_le_right : U ⊓ V ≤ V))]
    (F : ModuleDerived.{z} (crystallineSourceSite c)) :
    ∃ δ :
        (modulePushforwardDerived.{z} f).obj
            ((modulePushforwardDerived.{z} (crystallineOpenInclusion c U)).obj
              ((modulePushforwardDerived.{z}
                  (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U))).obj
                (crystallineRestrictedModule.{z}
                  (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U))
                  (crystallineRestrictedModule.{z} (crystallineOpenInclusion c U) F)))) ⟶
          (shiftFunctor (ModuleDerived.{z} (crystallineTargetSite c)) (1 : ℤ)).obj
            ((modulePushforwardDerived.{z} f).obj F),
      Triangle.mk
          (biprod.lift
            (crystallineDerivedRestrictionUnit.{z} f (crystallineOpenInclusion c U) F)
            (crystallineDerivedRestrictionUnit.{z} f (crystallineOpenInclusion c V) F))
          (biprod.desc
            (crystallineDerivedOverlapRestriction.{z} f
              (crystallineOpenInclusion c U)
              (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U)) F)
            (-(crystallineDerivedOverlapRestriction.{z} f
                (crystallineOpenInclusion c V)
                (crystallineOpenInclusion_le c (inf_le_right : U ⊓ V ≤ V)) F ≫
              eqToHom
                (crystallineDerivedOverlapTarget_eq.{z} f
                  (crystallineOpenInclusion c U) (crystallineOpenInclusion c V)
                  (crystallineOpenInclusion_le c (inf_le_left : U ⊓ V ≤ U))
                  (crystallineOpenInclusion_le c (inf_le_right : U ⊓ V ≤ V)) F))))
          δ ∈
        distTriang (ModuleDerived.{z} (crystallineTargetSite c)) := sorry

end AlgebraicGeometry.Scheme.Crystalline

end
