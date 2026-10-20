/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.SheafEquivalence
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Remark_75_6_3
public import stacks_project.Chap76.Definition_76_21_1_NaiveCotangent

/-!
# Comparison of naive cotangent complexes of representable algebraic spaces with schemes

A morphism of representable algebraic spaces over a scheme `S` is induced by a morphism
of schemes `f0 : X0 ⟶ Y0`. The complex `ε* NL_{X0/Y0}` is the underived module pullback of
`Scheme.Hom.naiveCotangent f0.left` along the ringed-site morphism `ε` of Section 75.4,
after transporting scheme modules to the small Zariski ringed site. Functoriality of
naive cotangent complexes along the `ε`-square identifies this pullback with `NL_{X/Y}`
in `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.Scheme.SiteRestriction
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open ComplexShape
open RingedSite.Hom
open Algebra Algebra.Extension Algebra.Generators
open Opposite MvPolynomial
open SheafOfModules.RingedSite
open CategoryTheory.Sheaf.FreeAlgebra
open scoped AlgebraicGeometry.AlgebraicSpace ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent

variable {S : Scheme.{u}}

/-- The identity-on-data functor from scheme modules to ringed-space modules is additive. -/
instance schemeModulesToRingedSpace_additive (X : Scheme.{u}) :
    (Scheme.Modules.toRingedSpace X).Additive :=
  sorry

/-- The identity-on-data functor from ringed-space modules to opens-site modules is
additive. -/
instance toOpensModules_additive (X : Scheme.{u}) :
    (toOpensModules X).Additive :=
  sorry

/-- Underived transport of unbounded cochain complexes of `𝒪_X`-modules to the small
Zariski ringed site of `X`. -/
def schemeToZariskiComplex (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤
      CochainComplex (RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite X)) ℤ :=
  (Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℤ) ⋙
    (toOpensModules X).mapHomologicalComplex (up ℤ) ⋙
      (opensToSmallZariski X).modulePushforwardComplex.{u} ⋙
        (smallZariskiToZariskiSmall X).modulePushforwardComplex.{u}

/-- Unfolding of `schemeToZariskiComplex` as the composite of the Zariski-site transports. -/
theorem schemeToZariskiComplex_eq (X : Scheme.{u}) :
    schemeToZariskiComplex X =
      (Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℤ) ⋙
        (toOpensModules X).mapHomologicalComplex (up ℤ) ⋙
          (opensToSmallZariski X).modulePushforwardComplex.{u} ⋙
            (smallZariskiToZariskiSmall X).modulePushforwardComplex.{u} :=
  sorry

/-- The morphism of ringed sites `ε` from the small étale site of `ofOver X0` to the
small Zariski site of `X0.left`. -/
def ofOverEpsilon (X0 : Over S) :
    RingedSite.Hom (ringedSite (ofOver X0)) (Scheme.Zariski.Small.ringedSite X0.left) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom X0) (smallEtaleToZariski X0.left)

/-- `ofOverEpsilon` is the composite of `schemeEtaleRingedHom` with
`smallEtaleToZariski`. -/
theorem ofOverEpsilon_eq (X0 : Over S) :
    ofOverEpsilon X0 =
      RingedSite.Hom.comp (schemeEtaleRingedHom X0) (smallEtaleToZariski X0.left) :=
  sorry

/-- Inverse image of the scheme-level naive cotangent complex of `f0.left` along `ε`, as the
successive underived module pullback of the Zariski transport of
`Scheme.Hom.naiveCotangent f0.left`. -/
def epsilonStarComplex {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    CochainComplex (ofOver X0).Modules ℤ :=
  (schemeEtaleRingedHom X0).modulePullbackComplex.{u}.obj
    ((smallEtaleToZariski X0.left).modulePullbackComplex.{u}.obj
      ((schemeToZariskiComplex X0.left).obj (Scheme.Hom.naiveCotangent f0.left)))

/-- `epsilonStarComplex f0` is the successive underived pullback of the Zariski transport of
`Scheme.Hom.naiveCotangent f0.left` along `smallEtaleToZariski` and `schemeEtaleRingedHom`. -/
theorem epsilonStarComplex_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarComplex f0 =
      (schemeEtaleRingedHom X0).modulePullbackComplex.{u}.obj
        ((smallEtaleToZariski X0.left).modulePullbackComplex.{u}.obj
          ((schemeToZariskiComplex X0.left).obj (Scheme.Hom.naiveCotangent f0.left))) :=
  sorry

/-- The degree `-1` term of `epsilonStarComplex` is the successive module pullback of the
degree `-1` term of the Zariski transport of `Scheme.Hom.naiveCotangent f0.left`. -/
theorem epsilonStarComplex_X_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X (-1) =
      (schemeEtaleRingedHom X0).modulePullback.{u}.obj
        ((smallEtaleToZariski X0.left).modulePullback.{u}.obj
          (((schemeToZariskiComplex X0.left).obj
              (Scheme.Hom.naiveCotangent f0.left)).X (-1))) :=
  sorry

/-- The degree `0` term of `epsilonStarComplex` is the successive module pullback of the
degree `0` term of the Zariski transport of `Scheme.Hom.naiveCotangent f0.left`. -/
theorem epsilonStarComplex_X_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X 0 =
      (schemeEtaleRingedHom X0).modulePullback.{u}.obj
        ((smallEtaleToZariski X0.left).modulePullback.{u}.obj
          (((schemeToZariskiComplex X0.left).obj
              (Scheme.Hom.naiveCotangent f0.left)).X 0)) :=
  sorry

/-- The commutative structure sheaf on the small Zariski site of a scheme. -/
def zariskiCommStructureSheaf (X : Scheme.{u}) :
    Sheaf X.smallZariskiTopology CommRingCat.{u} :=
  ⟨(Scheme.smallZariskiToScheme X).op ⋙ Scheme.Γ, sorry⟩

/-- The underlying presheaf of `zariskiCommStructureSheaf` is global sections. -/
theorem zariskiCommStructureSheaf_val (X : Scheme.{u}) :
    (zariskiCommStructureSheaf X).obj =
      (Scheme.smallZariskiToScheme X).op ⋙ Scheme.Γ :=
  rfl

/-- The base of `ofOverEpsilon` is continuous for the small Zariski and small étale topologies. -/
instance ofOverEpsilon_base_isContinuous (X0 : Over S) :
    (ofOverEpsilon X0).base.IsContinuous
      X0.left.smallZariskiTopology (smallEtaleTopology (ofOver X0)) :=
  sorry

/-- The base of a small-Zariski ringed-site morphism is continuous. -/
instance zariskiRingedHom_base_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Zariski.Small.ringedHom f).base.IsContinuous
      Y.smallZariskiTopology X.smallZariskiTopology :=
  sorry

/-- Commutative-ring pushforward along `ofOverEpsilon` admits a left adjoint. -/
instance ofOverEpsilon_sheafPushforwardContinuous_commRing_isRightAdjoint (X0 : Over S) :
    ((ofOverEpsilon X0).base.sheafPushforwardContinuous CommRingCat.{u}
      X0.left.smallZariskiTopology
      (smallEtaleTopology (ofOver X0))).IsRightAdjoint :=
  sorry

/-- Commutative-ring pushforward along a small-Zariski ringed-site morphism admits a left
adjoint. -/
instance zariskiRingedHom_sheafPushforwardContinuous_commRing_isRightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((Scheme.Zariski.Small.ringedHom f).base.sheafPushforwardContinuous CommRingCat.{u}
      Y.smallZariskiTopology X.smallZariskiTopology).IsRightAdjoint :=
  sorry

/-- Inverse image of a commutative-ring sheaf on the small Zariski site of `X0.left` along
`ε`. -/
def epsilonInverseImage (X0 : Over S)
    (R : Sheaf X0.left.smallZariskiTopology CommRingCat.{u}) :
    Sheaf (smallEtaleTopology (ofOver X0)) CommRingCat.{u} :=
  ((ofOverEpsilon X0).base.sheafPullback CommRingCat.{u}
      X0.left.smallZariskiTopology
      (smallEtaleTopology (ofOver X0))).obj R

/-- Inverse image of a morphism of commutative-ring sheaves along `ε`. -/
def epsilonInverseImageMap (X0 : Over S)
    {R R' : Sheaf X0.left.smallZariskiTopology CommRingCat.{u}} (α : R ⟶ R') :
    epsilonInverseImage X0 R ⟶ epsilonInverseImage X0 R' :=
  ((ofOverEpsilon X0).base.sheafPullback CommRingCat.{u}
      X0.left.smallZariskiTopology
      (smallEtaleTopology (ofOver X0))).map α

/-- Unfolding of `epsilonInverseImage` as sheaf pullback along the base of `ofOverEpsilon`. -/
theorem epsilonInverseImage_eq (X0 : Over S)
    (R : Sheaf X0.left.smallZariskiTopology CommRingCat.{u}) :
    epsilonInverseImage X0 R =
      ((ofOverEpsilon X0).base.sheafPullback CommRingCat.{u}
          X0.left.smallZariskiTopology
          (smallEtaleTopology (ofOver X0))).obj R :=
  sorry

/-- Inverse image of the small-Zariski structure sheaf of `Y` along a morphism of schemes. -/
def schemeInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallZariskiTopology CommRingCat.{u} :=
  ((Scheme.Zariski.Small.ringedHom f).base.sheafPullback CommRingCat.{u}
      Y.smallZariskiTopology X.smallZariskiTopology).obj
    (zariskiCommStructureSheaf Y)

/-- Unfolding of `schemeInverseImage` as sheaf pullback along the small-Zariski ringed
morphism. -/
theorem schemeInverseImage_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeInverseImage f =
      ((Scheme.Zariski.Small.ringedHom f).base.sheafPullback CommRingCat.{u}
          Y.smallZariskiTopology X.smallZariskiTopology).obj
        (zariskiCommStructureSheaf Y) :=
  sorry

/-- Pushforward form of `ε^♯` as a morphism of commutative-ring sheaves on the small Zariski
site. -/
def epsilonStructureSheafMapComm (X0 : Over S) :
    zariskiCommStructureSheaf X0.left ⟶
      ((ofOverEpsilon X0).base.sheafPushforwardContinuous CommRingCat.{u}
        X0.left.smallZariskiTopology
        (smallEtaleTopology (ofOver X0))).obj
        (commStructureSheaf (ofOver X0)) :=
  InducedCategory.homMk
    { app := fun V ↦
        CommRingCat.ofHom ((ofOverEpsilon X0).structureSheafMap.hom.app V).hom
      naturality := fun _ _ _ ↦ sorry }

/-- The inverse-image form `ε^♯ : ε⁻¹ 𝒪_{X0} ⟶ 𝒪_X` on the small étale site of
`ofOver X0`. -/
def epsilonSharp (X0 : Over S) :
    epsilonInverseImage X0 (zariskiCommStructureSheaf X0.left) ⟶
      commStructureSheaf (ofOver X0) :=
  (((ofOverEpsilon X0).base.sheafAdjunctionContinuous CommRingCat.{u}
        X0.left.smallZariskiTopology
        (smallEtaleTopology (ofOver X0))).homEquiv
      (zariskiCommStructureSheaf X0.left) (commStructureSheaf (ofOver X0))).symm
    (epsilonStructureSheafMapComm X0)

/-- Unfolding of `epsilonSharp` as the adjunct of `epsilonStructureSheafMapComm`. -/
theorem epsilonSharp_eq (X0 : Over S) :
    epsilonSharp X0 =
      (((ofOverEpsilon X0).base.sheafAdjunctionContinuous CommRingCat.{u}
            X0.left.smallZariskiTopology
            (smallEtaleTopology (ofOver X0))).homEquiv
          (zariskiCommStructureSheaf X0.left)
          (commStructureSheaf (ofOver X0))).symm
        (epsilonStructureSheafMapComm X0) :=
  sorry

/-- Pushforward form of the small-Zariski algebra map of a morphism of schemes. -/
def schemeAlgebraPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    zariskiCommStructureSheaf Y ⟶
      ((Scheme.Zariski.Small.ringedHom f).base.sheafPushforwardContinuous CommRingCat.{u}
        Y.smallZariskiTopology X.smallZariskiTopology).obj
        (zariskiCommStructureSheaf X) :=
  InducedCategory.homMk
    { app := fun V ↦
        CommRingCat.ofHom
          ((Scheme.Zariski.Small.ringedHom f).structureSheafMap.hom.app V).hom
      naturality := fun _ _ _ ↦ sorry }

/-- The inverse-image algebra map `f0^♯ : f0⁻¹ 𝒪_{Y0} ⟶ 𝒪_{X0}` on the small Zariski site. -/
def schemeAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeInverseImage f ⟶ zariskiCommStructureSheaf X :=
  (((Scheme.Zariski.Small.ringedHom f).base.sheafAdjunctionContinuous CommRingCat.{u}
        Y.smallZariskiTopology X.smallZariskiTopology).homEquiv
      (zariskiCommStructureSheaf Y) (zariskiCommStructureSheaf X)).symm
    (schemeAlgebraPushforward f)

/-- Unfolding of `schemeAlgebra` as the adjunct of `schemeAlgebraPushforward`. -/
theorem schemeAlgebra_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeAlgebra f =
      (((Scheme.Zariski.Small.ringedHom f).base.sheafAdjunctionContinuous CommRingCat.{u}
            Y.smallZariskiTopology X.smallZariskiTopology).homEquiv
          (zariskiCommStructureSheaf Y) (zariskiCommStructureSheaf X)).symm
        (schemeAlgebraPushforward f) :=
  sorry

/-- Inverse image along `ε` of the Zariski algebra map of `f0`. -/
def epsilonInverseImageSchemeAlgebra {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImage X0 (schemeInverseImage f0.left) ⟶
      epsilonInverseImage X0 (zariskiCommStructureSheaf X0.left) :=
  epsilonInverseImageMap X0 (schemeAlgebra f0.left)

/-- Unfolding of `epsilonInverseImageSchemeAlgebra` as `epsilonInverseImageMap` of
`schemeAlgebra`. -/
theorem epsilonInverseImageSchemeAlgebra_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageSchemeAlgebra f0 =
      epsilonInverseImageMap X0 (schemeAlgebra f0.left) :=
  sorry

/-- Inverse image of a commutative-ring sheaf along a morphism of algebraic spaces. -/
def commSheafInverseImageObj {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  fromInternalObj.{u + 1, u, u}
    ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R))

/-- Inverse image of a morphism of commutative-ring sheaves along a morphism of algebraic
spaces. -/
def commSheafInverseImageMap {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R') :
    commSheafInverseImageObj h R ⟶ commSheafInverseImageObj h R' :=
  fromInternalMap.{u + 1, u, u}
    ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α))

/-- Inverse image of `ε_Y⁻¹ 𝒪_{Y0}` along `ofOverMap f0`. -/
def pulledEpsilonInverseImage {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    Sheaf (smallEtaleTopology (ofOver X0)) CommRingCat.{u} :=
  commSheafInverseImageObj (ofOverMap f0)
    (epsilonInverseImage Y0 (zariskiCommStructureSheaf Y0.left))

/-- Compatibility map `f⁻¹(ε_Y⁻¹ 𝒪_{Y0}) ⟶ f_small⁻¹ 𝒪_Y` obtained by inverse image of
`ε_Y^♯`. -/
def pulledEpsilonSharp {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    pulledEpsilonInverseImage f0 ⟶ commInverseImageStructureSheaf (ofOverMap f0) :=
  commSheafInverseImageMap (ofOverMap f0) (epsilonSharp Y0)

/-- Unfolding of `pulledEpsilonSharp` as inverse image of `epsilonSharp`. -/
theorem pulledEpsilonSharp_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    pulledEpsilonSharp f0 =
      commSheafInverseImageMap (ofOverMap f0) (epsilonSharp Y0) :=
  sorry

/-- Coefficient map `ε⁻¹ f0⁻¹ 𝒪_{Y0} ⟶ f_small⁻¹ 𝒪_Y` of the `ε`-square, as inverse image
of `ε_Y^♯`. -/
def ofOverInverseImageCoeff {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    pulledEpsilonInverseImage f0 ⟶ commInverseImageStructureSheaf (ofOverMap f0) :=
  pulledEpsilonSharp f0

/-- Unfolding of `ofOverInverseImageCoeff` as `pulledEpsilonSharp`. -/
theorem ofOverInverseImageCoeff_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverInverseImageCoeff f0 = pulledEpsilonSharp f0 :=
  sorry

/-- Source algebra of the `ε`-square, as `ε^{-1} f0^♯` after transporting the inverse image
of `𝒪_{Y0}` along `ofOverMap`. -/
def ofOverSquareSourceAlgebra {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    pulledEpsilonInverseImage f0 ⟶ commStructureSheaf (ofOver X0) :=
  pulledEpsilonSharp f0 ≫ commInverseImageStructureSheafMap (ofOverMap f0)

/-- Unfolding of `ofOverSquareSourceAlgebra` as `pulledEpsilonSharp` followed by
`f_small^♯`. -/
theorem ofOverSquareSourceAlgebra_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverSquareSourceAlgebra f0 =
      pulledEpsilonSharp f0 ≫ commInverseImageStructureSheafMap (ofOverMap f0) :=
  sorry

/-- Module pushforward along `ofOverEpsilon` is a right adjoint. -/
instance ofOverEpsilon_modulePushforward_isRightAdjoint (X0 : Over S) :
    ((ofOverEpsilon X0).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Module pushforward along `schemeEtaleRingedHom` is a right adjoint. -/
instance schemeEtaleRingedHom_modulePushforward_isRightAdjoint (X0 : Over S) :
    ((schemeEtaleRingedHom X0).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Module pushforward along `smallEtaleToZariski` is a right adjoint. -/
instance smallEtaleToZariski_modulePushforward_isRightAdjoint (X : Scheme.{u}) :
    ((smallEtaleToZariski X).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- The étale chart of `ofOver X0` corresponding to a small Zariski open of `X0.left`. -/
def ofOverHom_chart (X0 : Over S) (U : X0.left.smallZariskiSiteᵒᵖ) :
    (smallEtaleSite (ofOver X0))ᵒᵖ :=
  op ((ofOverEpsilon X0).base.obj U.unop)

/-- `ofOverHom_chart` is evaluation of the base of `ofOverEpsilon`. -/
theorem ofOverHom_chart_eq (X0 : Over S) (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_chart X0 U = op ((ofOverEpsilon X0).base.obj U.unop) :=
  sorry

/-- The open range in `X0.left` of a small Zariski object. -/
abbrev ofOverHom_opensRange (X0 : Over S) (U : X0.left.smallZariskiSiteᵒᵖ) :
    X0.left.Opens :=
  (Scheme.smallZariskiRangeFunctor X0.left).obj U.unop

/-- `ofOverHom_opensRange` is the open range of the underlying open immersion. -/
theorem ofOverHom_opensRange_eq (X0 : Over S) (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_opensRange X0 U =
      (Scheme.smallZariskiRangeFunctor X0.left).obj U.unop :=
  sorry

/-- Canonical identification `Γ(U, 𝒪_U) ≅ Γ(X0, U.opensRange)` of `IsOpenImmersion.ΓIsoTop`. -/
def ofOverHom_gammaIso (X0 : Over S) (U : X0.left.smallZariskiSiteᵒᵖ) :
    (zariskiCommStructureSheaf X0.left).obj.obj U ≅
      Γ(X0.left, ofOverHom_opensRange X0 U) :=
  @IsOpenImmersion.ΓIsoTop U.unop.left X0.left U.unop.hom U.unop.prop

/-- Unfolding of `ofOverHom_gammaIso` as `IsOpenImmersion.ΓIsoTop`. -/
theorem ofOverHom_gammaIso_eq (X0 : Over S) (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_gammaIso X0 U =
      @IsOpenImmersion.ΓIsoTop U.unop.left X0.left U.unop.hom U.unop.prop :=
  sorry


/-- Canonical identification `Γ(U, 𝒪_U) ≅ Γ(Y, U)` of an open immersion `U.ι`. -/
def ofOverHom_opensGammaIso (Y : Scheme.{u}) (V : Y.Opens) :
    (zariskiCommStructureSheaf Y).obj.obj
        (op ((Scheme.smallZariskiOpenFunctor Y).obj V)) ≅
      Y.sheaf.obj.obj (op V) :=
  @IsOpenImmersion.ΓIsoTop
      ((Scheme.smallZariskiOpenFunctor Y).obj V).left Y
      ((Scheme.smallZariskiOpenFunctor Y).obj V).hom
      ((Scheme.smallZariskiOpenFunctor Y).obj V).prop ≪≫
    Y.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι (U := V)).symm).op

/-- Unfolding of `ofOverHom_opensGammaIso` as `ΓIsoTop` followed by `opensRange_ι`. -/
theorem ofOverHom_opensGammaIso_eq (Y : Scheme.{u}) (V : Y.Opens) :
    ofOverHom_opensGammaIso Y V =
      @IsOpenImmersion.ΓIsoTop
          ((Scheme.smallZariskiOpenFunctor Y).obj V).left Y
          ((Scheme.smallZariskiOpenFunctor Y).obj V).hom
          ((Scheme.smallZariskiOpenFunctor Y).obj V).prop ≪≫
        Y.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι (U := V)).symm).op :=
  sorry

/-- Direct-image form of the comparison from `𝒪_Y` to the transport of the small-Zariski
inverse image of `𝒪_Y` along `f`. -/
def ofOverHom_schemeInverseImagePushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.toShHom.hom.base).obj
        ((Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).functor.obj (schemeInverseImage f)) :=
  ⟨{ app := fun V ↦
        (ofOverHom_opensGammaIso Y V.unop).inv ≫
          (((Scheme.Zariski.Small.ringedHom f).base.sheafAdjunctionContinuous CommRingCat.{u}
              Y.smallZariskiTopology X.smallZariskiTopology).unit.app
            (zariskiCommStructureSheaf Y)).hom.app
            (op ((Scheme.smallZariskiOpenFunctor Y).obj V.unop)) ≫
          (schemeInverseImage f).obj.map
            ((Scheme.smallZariskiPullbackOpenFunctorIso f).inv.app V.unop).op
     naturality := fun _ _ _ ↦ sorry }⟩

/-- Adjunct comparison from the topological inverse image `f⁻¹𝒪_Y` to the transported
small-Zariski inverse image. -/
def ofOverHom_opensInverseImageCompareInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf ⟶
      (Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).functor.obj (schemeInverseImage f) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      f.toShHom.hom.base).homEquiv
      Y.sheaf
      ((Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).functor.obj
        (schemeInverseImage f))).symm
    (ofOverHom_schemeInverseImagePushforwardUnit f)

/-- Unfolding of `ofOverHom_opensInverseImageCompareInv` as the adjunct of
`ofOverHom_schemeInverseImagePushforwardUnit`. -/
theorem ofOverHom_opensInverseImageCompareInv_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ofOverHom_opensInverseImageCompareInv f =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          f.toShHom.hom.base).homEquiv
          Y.sheaf
          ((Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).functor.obj
            (schemeInverseImage f))).symm
        (ofOverHom_schemeInverseImagePushforwardUnit f) :=
  sorry

/-- The adjunct comparison of inverse images of `𝒪_Y` is an isomorphism of sheaves on the
opens site. -/
instance ofOverHom_opensInverseImageCompareInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (ofOverHom_opensInverseImageCompareInv f) :=
  sorry

/-- Comparison of the small-Zariski inverse image of `𝒪_Y`, transported to the opens site,
with the topological inverse image `f⁻¹𝒪_Y`. -/
def ofOverHom_opensInverseImageCompare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).functor.obj (schemeInverseImage f) ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf :=
  CategoryTheory.inv (ofOverHom_opensInverseImageCompareInv f)

/-- Site-equivalence comparison from the small-Zariski inverse image of `𝒪_Y` to the
opens-site inverse image. -/
def ofOverHom_schemeInverseImageToOpens {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeInverseImage f ⟶
      (Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).inverse.obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf) :=
  ((Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).unitIso.app
      (schemeInverseImage f)).hom ≫
    (Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).inverse.map
      (ofOverHom_opensInverseImageCompare f)

/-- Unfolding of `ofOverHom_schemeInverseImageToOpens` as the sheaf-equivalence unit followed
by inverse-image comparison. -/
theorem ofOverHom_schemeInverseImageToOpens_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ofOverHom_schemeInverseImageToOpens f =
      ((Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).unitIso.app
          (schemeInverseImage f)).hom ≫
        (Scheme.smallZariskiSheafEquiv X CommRingCat.{u}).inverse.map
          (ofOverHom_opensInverseImageCompare f) :=
  sorry


/-- Evaluation of `ε_* ε⁻¹` at a small Zariski open recovers sections of `ε⁻¹` at the
corresponding `ε`-chart. -/
theorem ofOverUnitTarget_obj_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (((ofOverEpsilon X0).base.sheafPushforwardContinuous CommRingCat.{u}
          X0.left.smallZariskiTopology
          (smallEtaleTopology (ofOver X0))).obj
        (epsilonInverseImage X0 (schemeInverseImage f0.left))).obj.obj U =
      (epsilonInverseImage X0 (schemeInverseImage f0.left)).obj.obj
        (ofOverHom_chart X0 U) :=
  sorry

/-- Beck–Chevalley identification `ε⁻¹ f0⁻¹ 𝒪_{Y0} = f⁻¹(ε_Y⁻¹ 𝒪_{Y0})` at an `ε`-chart. -/
theorem ofOverBeckChevalley_obj_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (epsilonInverseImage X0 (schemeInverseImage f0.left)).obj.obj (ofOverHom_chart X0 U) =
      (pulledEpsilonInverseImage f0).obj.obj (ofOverHom_chart X0 U) :=
  sorry

/-- Objectwise coefficient `ε⁻¹ f0⁻¹ 𝒪_{Y0}(U) ⟶ f_small⁻¹ 𝒪_Y(ε(U))`. -/
def ofOverInverseImageCoeffApp {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (schemeInverseImage f0.left).obj.obj U ⟶
      (commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U) :=
  (((ofOverEpsilon X0).base.sheafAdjunctionContinuous CommRingCat.{u}
        X0.left.smallZariskiTopology
        (smallEtaleTopology (ofOver X0))).unit.app
      (schemeInverseImage f0.left)).hom.app U ≫
    eqToHom (ofOverUnitTarget_obj_eq f0 U) ≫
      eqToHom (ofOverBeckChevalley_obj_eq f0 U) ≫
        (pulledEpsilonSharp f0).hom.app (ofOverHom_chart X0 U)

/-- Unfolding of `ofOverInverseImageCoeffApp` as the adjunction unit, Beck–Chevalley
comparison, and `pulledEpsilonSharp`. -/
theorem ofOverInverseImageCoeffApp_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverInverseImageCoeffApp f0 U =
      (((ofOverEpsilon X0).base.sheafAdjunctionContinuous CommRingCat.{u}
            X0.left.smallZariskiTopology
            (smallEtaleTopology (ofOver X0))).unit.app
          (schemeInverseImage f0.left)).hom.app U ≫
        eqToHom (ofOverUnitTarget_obj_eq f0 U) ≫
          eqToHom (ofOverBeckChevalley_obj_eq f0 U) ≫
            (pulledEpsilonSharp f0).hom.app (ofOverHom_chart X0 U) :=
  sorry

/-- Structure-sheaf coefficient `𝒪_{X0}(U) ⟶ 𝒪_X(ε(U))` of `ε^♯`. -/
def ofOverStructureCoeff {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (zariskiCommStructureSheaf X0.left).obj.obj U ⟶
      (commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U) :=
  CommRingCat.ofHom ((ofOverEpsilon X0).structureSheafMap.hom.app U).hom

/-- The algebra structure on `𝒪_{X0}(U)` over `f0⁻¹𝒪_{Y0}(U)`. -/
@[reducible] def schemeInverseImageAlgebra {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    Algebra ((schemeInverseImage f0.left).obj.obj U)
      ((zariskiCommStructureSheaf X0.left).obj.obj U) :=
  ((schemeAlgebra f0.left).hom.app U).hom.toAlgebra

/-- The canonical self-presentation of `𝒪_{X0}(U)` over `f0⁻¹𝒪_{Y0}(U)`. -/
def schemePresentation {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  @Generators.self
    ((schemeInverseImage f0.left).obj.obj U)
    ((zariskiCommStructureSheaf X0.left).obj.obj U)
    _ _ (schemeInverseImageAlgebra f0 U)

/-- Objectwise degree `-1` term of the scheme-level naive cotangent at a small Zariski open. -/
def schemeCotangentObj {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ModuleCat.{u} ((zariskiCommStructureSheaf X0.left).obj.obj U) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  ModuleCat.of _ (schemePresentation f0 U).toExtension.Cotangent

/-- Objectwise degree `0` term of the scheme-level naive cotangent at a small Zariski open. -/
def schemeCotangentSpaceObj {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ModuleCat.{u} ((zariskiCommStructureSheaf X0.left).obj.obj U) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  ModuleCat.of _ (schemePresentation f0 U).toExtension.CotangentSpace

/-- Polynomial-ring map of canonical presentations induced by the `ε`-square. -/
def ofOverPresentationRingHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    MvPolynomial ((zariskiCommStructureSheaf X0.left).obj.obj U)
        ((schemeInverseImage f0.left).obj.obj U) →+*
      MvPolynomial ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U))
        ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U)) :=
  (MvPolynomial.map (ofOverInverseImageCoeffApp f0 U).hom).comp
    (MvPolynomial.rename fun s ↦ (ofOverStructureCoeff f0 U).hom s).toRingHom

/-- Algebra homomorphism of canonical presentations induced by the `ε`-square. -/
def ofOverPresentationAlgHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  ({ ofOverPresentationRingHom f0 U with
      commutes' := fun _ ↦ sorry } :
    MvPolynomial ((zariskiCommStructureSheaf X0.left).obj.obj U)
        ((schemeInverseImage f0.left).obj.obj U) →ₐ[
      (schemeInverseImage f0.left).obj.obj U]
      MvPolynomial ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U))
        ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U)))

/-- Kernel compatibility of the `ε`-square presentation map. -/
theorem ofOverPresentationKer_le_comap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
    letI := schemeInverseImageAlgebra f0 U
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
    letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
    (schemePresentation f0 U).ker ≤
      (presentation (ofOverMap f0) (ofOverHom_chart X0 U)).ker.comap
        (ofOverPresentationRingHom f0 U) :=
  sorry

/-- Scalar tower of the coefficient map through `f_small⁻¹ 𝒪_Y`. -/
theorem ofOver_isScalarTower_inverseImage {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
    letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
    letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
    -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
    letI : Algebra
        ((schemeInverseImage f0.left).obj.obj U)
        ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
            (ofOverHom_chart X0 U)).hom.comp
          (ofOverInverseImageCoeffApp f0 U).hom)
    IsScalarTower
      ((schemeInverseImage f0.left).obj.obj U)
      ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U))
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
  sorry

/-- Scalar tower of `f0^♯` and `ε^♯` into `𝒪_X(ε(U))`. -/
theorem ofOver_isScalarTower_structure {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
    letI := schemeInverseImageAlgebra f0 U
    -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
    letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
    -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
    letI : Algebra
        ((schemeInverseImage f0.left).obj.obj U)
        ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
            (ofOverHom_chart X0 U)).hom.comp
          (ofOverInverseImageCoeffApp f0 U).hom)
    IsScalarTower
      ((schemeInverseImage f0.left).obj.obj U)
      ((zariskiCommStructureSheaf X0.left).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
  sorry

/-- Morphism of canonical presentations induced by the `ε`-square. -/
def ofOverPresentationHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
  letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      ((schemeInverseImage f0.left).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `f⁻¹𝒪_Y`.
  letI := ofOver_isScalarTower_inverseImage f0 U
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_{X0}(U)`.
  letI := ofOver_isScalarTower_structure f0 U
  ({ toRingHom := ofOverPresentationRingHom f0 U
     toRingHom_algebraMap := fun _ ↦ sorry
     algebraMap_toRingHom := fun _ ↦ sorry } :
    ((schemePresentation f0 U).toExtension).Hom
      ((presentation (ofOverMap f0) (ofOverHom_chart X0 U)).toExtension))

/-- Sheafification unit of the space-level conormal presheaf, evaluated at an `ε`-chart. -/
def ofOverHom_negOne_sheafUnit {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    cotangentObj (ofOverMap f0) (ofOverHom_chart X0 U) ⟶
      ((SheafOfModules.forget _).obj
        (cotangentSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U) :=
  ((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf (ofOver X0)).obj)).unit.app
    (cotangentPresheaf (ofOverMap f0))).app (ofOverHom_chart X0 U)

/-- Sheafification unit of the space-level cotangent-space presheaf, evaluated at an `ε`-chart. -/
def ofOverHom_zero_sheafUnit {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    cotangentSpaceObj (ofOverMap f0) (ofOverHom_chart X0 U) ⟶
      ((SheafOfModules.forget _).obj
        (cotangentSpaceSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U) :=
  ((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf (ofOver X0)).obj)).unit.app
    (cotangentSpacePresheaf (ofOverMap f0))).app (ofOverHom_chart X0 U)

/-- Objectwise comparison of conormal terms of the `ε`-square. -/
def ofOverHom_negOne_section {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    schemeCotangentObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (cotangentObj (ofOverMap f0) (ofOverHom_chart X0 U)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  ConcreteCategory.ofHom
    (C := ModuleCat ((zariskiCommStructureSheaf X0.left).obj.obj U))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (schemePresentation f0 U).ker
            (presentation (ofOverMap f0) (ofOverHom_chart X0 U)).ker
            (ofOverPresentationAlgHom f0 U)
            (ofOverPresentationKer_le_comap f0 U)
            (Cotangent.val (P := (schemePresentation f0 U).toExtension) x))
      map_add' := sorry
      map_smul' := sorry }

/-- Objectwise comparison of presentation cotangent-space terms of the `ε`-square. -/
def ofOverHom_zero_section {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    schemeCotangentSpaceObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (cotangentSpaceObj (ofOverMap f0) (ofOverHom_chart X0 U)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
  letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      ((schemeInverseImage f0.left).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `f⁻¹𝒪_Y`.
  letI := ofOver_isScalarTower_inverseImage f0 U
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_{X0}(U)`.
  letI := ofOver_isScalarTower_structure f0 U
  ConcreteCategory.ofHom
    (C := ModuleCat ((zariskiCommStructureSheaf X0.left).obj.obj U))
    (CotangentSpace.map (ofOverPresentationHom f0 U))

/-- Objectwise Zariski-side degree `-1` comparison. -/
def ofOverHom_negOne_zariski_app {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    schemeCotangentObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (((SheafOfModules.forget _).obj
          (cotangentSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U)) :=
  ofOverHom_negOne_section f0 U ≫
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).map
      (ofOverHom_negOne_sheafUnit f0 U)

/-- Objectwise Zariski-side degree `0` comparison. -/
def ofOverHom_zero_zariski_app {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    schemeCotangentSpaceObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (((SheafOfModules.forget _).obj
          (cotangentSpaceSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U)) :=
  ofOverHom_zero_section f0 U ≫
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).map
      (ofOverHom_zero_sheafUnit f0 U)

/-- The sheaf polynomial presentation of `f0.left` on the opens site of `X0.left`. -/
abbrev ofOverHom_schemePresentation {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :=
  CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
    ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
    (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)

/-- Coefficient ring of the sheaf polynomial presentation of `f0.left` at the open range. -/
abbrev ofOverHom_schemePullback {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
    Y0.left.sheaf).obj.obj (op (ofOverHom_opensRange X0 U))

/-- Underlying ring of the sheaf polynomial presentation of `f0.left` at the open range. -/
abbrev ofOverHom_schemeUnderlying {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  (CategoryTheory.Sheaf.FreeAlgebra.Presentation.underlying
    ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
    (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)).obj.obj
    (op (ofOverHom_opensRange X0 U))

/-- Coefficient map from the opens-site inverse image of `𝒪_{Y0}` into the sheaf polynomial
presentation of `f0.left` at the open range. -/
def ofOverHom_negOne_affineCoeff {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_schemePullback f0 U ⟶ ofOverHom_schemeUnderlying f0 U :=
  CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
      ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
      (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom) |>.hom.app
      (op (ofOverHom_opensRange X0 U))

/-- Identification of the small-Zariski inverse image of `𝒪_{Y0}` with the opens-site
inverse image at the open range, via `smallZariskiSheafEquiv`. -/
def ofOverHom_negOne_coeffToPullback {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (schemeInverseImage f0.left).obj.obj U ⟶ ofOverHom_schemePullback f0 U :=
  (ofOverHom_schemeInverseImageToOpens f0.left).hom.app U

/-- AffineComparison-style polynomial map from the algebraic self-presentation of `f0.left`
at `U` into the sheaf polynomial presentation at the open range. -/
def ofOverHom_negOne_affinePolynomialMap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    MvPolynomial ((zariskiCommStructureSheaf X0.left).obj.obj U)
        ((schemeInverseImage f0.left).obj.obj U) →+* ofOverHom_schemeUnderlying f0 U :=
  MvPolynomial.eval₂Hom
    ((ofOverHom_negOne_affineCoeff f0 U).hom.comp (ofOverHom_negOne_coeffToPullback f0 U).hom)
    (fun s ↦
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
          ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)).hom.app
        (op (ofOverHom_opensRange X0 U))
        ((ofOverHom_gammaIso X0 U).hom s))

/-- The affine polynomial map as an algebra homomorphism over `f0⁻¹𝒪_{Y0}(U)`. -/
def ofOverHom_negOne_affinePolynomialAlgHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise coefficient of the sheaf presentation.
  letI := ((ofOverHom_negOne_affineCoeff f0 U).hom.comp
    (ofOverHom_negOne_coeffToPullback f0 U).hom).toAlgebra
  ({ ofOverHom_negOne_affinePolynomialMap f0 U with
      commutes' := fun _ ↦ sorry } :
    MvPolynomial ((zariskiCommStructureSheaf X0.left).obj.obj U)
        ((schemeInverseImage f0.left).obj.obj U) →ₐ[
      (schemeInverseImage f0.left).obj.obj U]
      ofOverHom_schemeUnderlying f0 U)

/-- Kernel compatibility of the affine polynomial map with the sheaf presentation. -/
theorem ofOverHom_negOne_affinePolynomialMap_mem_ker {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
    letI := schemeInverseImageAlgebra f0 U
    (schemePresentation f0 U).ker ≤
      (conormalIdeal (ofOverHom_schemePresentation f0)
          (op (ofOverHom_opensRange X0 U))).comap
        (ofOverHom_negOne_affinePolynomialMap f0 U) :=
  sorry

/-- Degree `-1` term of the transported scheme naive cotangent at a small Zariski open. -/
abbrev ofOverHom_negOne_unpacked {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  (((schemeToZariskiComplex X0.left).obj
      (Scheme.Hom.naiveCotangent f0.left)).X (-1)).val.obj U

/-- Degree `0` term of the transported scheme naive cotangent at a small Zariski open. -/
abbrev ofOverHom_zero_unpacked {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :=
  (((schemeToZariskiComplex X0.left).obj
      (Scheme.Hom.naiveCotangent f0.left)).X 0).val.obj U

/-- AffineComparison-style map from the algebraic self-presentation cotangent to the unpacked
sheaf-level scheme conormal. -/
def ofOverHom_negOne_affineHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    schemeCotangentObj f0 U ⟶ ofOverHom_negOne_unpacked f0 U :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise coefficient of the sheaf presentation.
  letI := ((ofOverHom_negOne_affineCoeff f0 U).hom.comp
    (ofOverHom_negOne_coeffToPullback f0 U).hom).toAlgebra
  ConcreteCategory.ofHom
    (C := ModuleCat ((zariskiCommStructureSheaf X0.left).obj.obj U))
    { toFun := fun x ↦
        ((conormalSourcePresheafUnit (ofOverHom_schemePresentation f0)).app
            (op (ofOverHom_opensRange X0 U))
          (Ideal.mapCotangent (schemePresentation f0 U).ker
            (conormalIdeal (ofOverHom_schemePresentation f0)
              (op (ofOverHom_opensRange X0 U)))
            (ofOverHom_negOne_affinePolynomialAlgHom f0 U)
            (ofOverHom_negOne_affinePolynomialMap_mem_ker f0 U)
            (Cotangent.val (P := (schemePresentation f0 U).toExtension) x)) :
          ofOverHom_negOne_unpacked f0 U)
      map_add' := sorry
      map_smul' := sorry }

/-- AffineComparison-style generator section of the sheaf-level degree `0` scheme naive
cotangent, after transport to a small Zariski open. -/
def ofOverHom_zero_affineSection {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ)
    (a : (zariskiCommStructureSheaf X0.left).obj.obj U) :
    ofOverHom_zero_unpacked f0 U :=
  ((extendRestrictAdj (ofOverHom_schemePresentation f0)).unit.app
      Ω(CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
        ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
        (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom))).val.app
    (op (ofOverHom_opensRange X0 U))
    (((relativeDifferential
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
          ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom))).app
        (op (ofOverHom_opensRange X0 U))).d
      ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
          ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)).hom.app
        (op (ofOverHom_opensRange X0 U))
        ((ofOverHom_gammaIso X0 U).hom a)))

/-- AffineComparison-style map from the algebraic self-presentation cotangent space to the
unpacked sheaf-level scheme cotangent space. -/
def ofOverHom_zero_affineHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    schemeCotangentSpaceObj f0 U ⟶ ofOverHom_zero_unpacked f0 U :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (defeq pin): use the module structure carried by the
  -- transported degree `0` scheme naive cotangent as the codomain of the basis map.
  let N := ofOverHom_zero_unpacked f0 U
  letI : Module ((zariskiCommStructureSheaf X0.left).obj.obj U) N := N.isModule
  let φ :=
    (schemePresentation f0 U).cotangentSpaceBasis.constr
      ((zariskiCommStructureSheaf X0.left).obj.obj U)
      (fun a ↦ (ofOverHom_zero_affineSection f0 U a : N))
  ConcreteCategory.ofHom
    (C := ModuleCat ((zariskiCommStructureSheaf X0.left).obj.obj U))
    { toFun := fun x ↦ φ x
      map_add' := sorry
      map_smul' := sorry }

/-- The affine comparison from the algebraic cotangent to the unpacked sheaf conormal is an
isomorphism on sections. -/
instance ofOverHom_negOne_affineHom_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    IsIso (ofOverHom_negOne_affineHom f0 U) :=
  sorry

/-- The affine comparison from the algebraic cotangent space to the unpacked sheaf term is an
isomorphism on sections. -/
instance ofOverHom_zero_affineHom_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    IsIso (ofOverHom_zero_affineHom f0 U) :=
  sorry

/-- AffineComparison-style inverse, from the unpacked sheaf-level scheme conormal to the
algebraic self-presentation cotangent. -/
def ofOverHom_negOne_affineInv {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_negOne_unpacked f0 U ⟶ schemeCotangentObj f0 U :=
  @CategoryTheory.inv _ _ _ _ (ofOverHom_negOne_affineHom f0 U)
    (ofOverHom_negOne_affineHom_isIso f0 U)

/-- AffineComparison-style inverse, from the unpacked sheaf-level scheme cotangent space to
the algebraic self-presentation cotangent space. -/
def ofOverHom_zero_affineInv {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_zero_unpacked f0 U ⟶ schemeCotangentSpaceObj f0 U :=
  @CategoryTheory.inv _ _ _ _ (ofOverHom_zero_affineHom f0 U)
    (ofOverHom_zero_affineHom_isIso f0 U)

/-- Opens-site transport of the unpacked degree `-1` scheme naive cotangent into the
successive small-Zariski pushforward. -/
def ofOverHom_negOne_transportHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_negOne_unpacked f0 U ⟶
      (((schemeToZariskiComplex X0.left).obj
          (Scheme.Hom.naiveCotangent f0.left)).X (-1)).val.obj U :=
  𝟙 _

/-- Inverse opens-site transport of the successive small-Zariski pushforward back to the
unpacked degree `-1` scheme naive cotangent. -/
def ofOverHom_negOne_transportInv {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (((schemeToZariskiComplex X0.left).obj
        (Scheme.Hom.naiveCotangent f0.left)).X (-1)).val.obj U ⟶
      ofOverHom_negOne_unpacked f0 U :=
  𝟙 _

/-- Opens-site transport of the unpacked degree `0` scheme naive cotangent into the
successive small-Zariski pushforward. -/
def ofOverHom_zero_transportHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    ofOverHom_zero_unpacked f0 U ⟶
      (((schemeToZariskiComplex X0.left).obj
          (Scheme.Hom.naiveCotangent f0.left)).X 0).val.obj U :=
  𝟙 _

/-- Inverse opens-site transport of the successive small-Zariski pushforward back to the
unpacked degree `0` scheme naive cotangent. -/
def ofOverHom_zero_transportInv {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (((schemeToZariskiComplex X0.left).obj
        (Scheme.Hom.naiveCotangent f0.left)).X 0).val.obj U ⟶
      ofOverHom_zero_unpacked f0 U :=
  𝟙 _

/-- Target packing of the space-level conormal sheaf as the pushforward along `ε`. -/
def ofOverHom_negOne_targetHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
      (((SheafOfModules.forget _).obj
        (cotangentSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U)) ⟶
      ((ofOverEpsilon X0).modulePushforward.{u}.obj
        (cotangentSheaf (ofOverMap f0))).val.obj U :=
  ConcreteCategory.ofHom
    (C := ModuleCat ((zariskiCommStructureSheaf X0.left).obj.obj U))
    { toFun := fun x ↦ x
      map_add' := sorry
      map_smul' := sorry }

/-- Target packing of the space-level cotangent-space sheaf as the pushforward along `ε`. -/
def ofOverHom_zero_targetHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.smallZariskiSiteᵒᵖ) :
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
      (((SheafOfModules.forget _).obj
        (cotangentSpaceSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U)) ⟶
      ((ofOverEpsilon X0).modulePushforward.{u}.obj
        (cotangentSpaceSheaf (ofOverMap f0))).val.obj U :=
  ConcreteCategory.ofHom
    (C := ModuleCat ((zariskiCommStructureSheaf X0.left).obj.obj U))
    { toFun := fun x ↦ x
      map_add' := sorry
      map_smul' := sorry }

/-- Zariski-side degree `-1` comparison, as opens-site transport, AffineComparison inverse,
`ε`-square functoriality, and target packing. -/
def ofOverHom_negOne_zariski {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ((schemeToZariskiComplex X0.left).obj
        (Scheme.Hom.naiveCotangent f0.left)).X (-1) ⟶
      (ofOverEpsilon X0).modulePushforward.{u}.obj (cotangentSheaf (ofOverMap f0)) where
  val := {
    app := fun U ↦
      ofOverHom_negOne_transportInv f0 U ≫
        ofOverHom_negOne_affineInv f0 U ≫
          ofOverHom_negOne_zariski_app f0 U ≫
            ofOverHom_negOne_targetHom f0 U
    naturality := sorry }

/-- Zariski-side degree `0` comparison, as opens-site transport, AffineComparison inverse,
`ε`-square functoriality, and target packing. -/
def ofOverHom_zero_zariski {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ((schemeToZariskiComplex X0.left).obj
        (Scheme.Hom.naiveCotangent f0.left)).X 0 ⟶
      (ofOverEpsilon X0).modulePushforward.{u}.obj (cotangentSpaceSheaf (ofOverMap f0)) where
  val := {
    app := fun U ↦
      ofOverHom_zero_transportInv f0 U ≫
        ofOverHom_zero_affineInv f0 U ≫
          ofOverHom_zero_zariski_app f0 U ≫
            ofOverHom_zero_targetHom f0 U
    naturality := sorry }

/-- The degree `-1` Zariski comparison unfolds to opens-site transport, the AffineComparison
inverse, `ε`-square functoriality, and target packing. -/
theorem ofOverHom_negOne_zariski_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom_negOne_zariski f0).val.app =
      fun U ↦
        ofOverHom_negOne_transportInv f0 U ≫
          ofOverHom_negOne_affineInv f0 U ≫
            ofOverHom_negOne_zariski_app f0 U ≫
              ofOverHom_negOne_targetHom f0 U :=
  sorry

/-- The degree `0` Zariski comparison unfolds to opens-site transport, the AffineComparison
inverse, `ε`-square functoriality, and target packing. -/
theorem ofOverHom_zero_zariski_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom_zero_zariski f0).val.app =
      fun U ↦
        ofOverHom_zero_transportInv f0 U ≫
          ofOverHom_zero_affineInv f0 U ≫
            ofOverHom_zero_zariski_app f0 U ≫
              ofOverHom_zero_targetHom f0 U :=
  sorry

/-- Intermediate étale-side degree `-1` comparison obtained by transposing
`ofOverHom_negOne_zariski` along `ofOverEpsilon`. -/
def ofOverHom_negOne_etale {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverEpsilon X0).modulePullback.{u}.obj
        (((schemeToZariskiComplex X0.left).obj
            (Scheme.Hom.naiveCotangent f0.left)).X (-1)) ⟶
      cotangentSheaf (ofOverMap f0) :=
  (modulePullbackHomEquiv.{u} (ofOverEpsilon X0)
      (((schemeToZariskiComplex X0.left).obj
          (Scheme.Hom.naiveCotangent f0.left)).X (-1))
      (cotangentSheaf (ofOverMap f0))).symm
    (ofOverHom_negOne_zariski f0)

/-- Intermediate étale-side degree `0` comparison obtained by transposing
`ofOverHom_zero_zariski` along `ofOverEpsilon`. -/
def ofOverHom_zero_etale {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverEpsilon X0).modulePullback.{u}.obj
        (((schemeToZariskiComplex X0.left).obj
            (Scheme.Hom.naiveCotangent f0.left)).X 0) ⟶
      cotangentSpaceSheaf (ofOverMap f0) :=
  (modulePullbackHomEquiv.{u} (ofOverEpsilon X0)
      (((schemeToZariskiComplex X0.left).obj
          (Scheme.Hom.naiveCotangent f0.left)).X 0)
      (cotangentSpaceSheaf (ofOverMap f0))).symm
    (ofOverHom_zero_zariski f0)

/-- Degree `-1` component of `(ε* NL_{X0/Y0}) ⟶ NL_{X/Y}`, as the adjunction transpose of
the Zariski-side `ε`-square conormal comparison. -/
def ofOverHom_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X (-1) ⟶ (naiveCotangent (ofOverMap f0)).X (-1) :=
  ((modulePullbackCompIso (schemeEtaleRingedHom X0)
      (smallEtaleToZariski X0.left)).inv.app
      (((schemeToZariskiComplex X0.left).obj
          (Scheme.Hom.naiveCotangent f0.left)).X (-1))) ≫
    ofOverHom_negOne_etale f0

/-- Degree `0` component of `(ε* NL_{X0/Y0}) ⟶ NL_{X/Y}`, as the adjunction transpose of
the Zariski-side `ε`-square cotangent-space comparison. -/
def ofOverHom_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X 0 ⟶ (naiveCotangent (ofOverMap f0)).X 0 :=
  ((modulePullbackCompIso (schemeEtaleRingedHom X0)
      (smallEtaleToZariski X0.left)).inv.app
      (((schemeToZariskiComplex X0.left).obj
          (Scheme.Hom.naiveCotangent f0.left)).X 0)) ≫
    ofOverHom_zero_etale f0

/-- `ofOverHom_negOne` is the composite of the pullback-composition comparison with the
`ε`-transpose of `ofOverHom_negOne_zariski`. -/
theorem ofOverHom_negOne_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHom_negOne f0 =
      ((modulePullbackCompIso (schemeEtaleRingedHom X0)
          (smallEtaleToZariski X0.left)).inv.app
          (((schemeToZariskiComplex X0.left).obj
              (Scheme.Hom.naiveCotangent f0.left)).X (-1))) ≫
        ofOverHom_negOne_etale f0 :=
  sorry

/-- `ofOverHom_zero` is the composite of the pullback-composition comparison with the
`ε`-transpose of `ofOverHom_zero_zariski`. -/
theorem ofOverHom_zero_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHom_zero f0 =
      ((modulePullbackCompIso (schemeEtaleRingedHom X0)
          (smallEtaleToZariski X0.left)).inv.app
          (((schemeToZariskiComplex X0.left).obj
              (Scheme.Hom.naiveCotangent f0.left)).X 0)) ≫
        ofOverHom_zero_etale f0 :=
  sorry

/-- `ofOverHom_negOne_etale` is the adjunction transpose of `ofOverHom_negOne_zariski`
along `ofOverEpsilon`. -/
theorem ofOverHom_negOne_etale_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHom_negOne_etale f0 =
      (modulePullbackHomEquiv.{u} (ofOverEpsilon X0)
          (((schemeToZariskiComplex X0.left).obj
              (Scheme.Hom.naiveCotangent f0.left)).X (-1))
          (cotangentSheaf (ofOverMap f0))).symm
        (ofOverHom_negOne_zariski f0) :=
  sorry

/-- `ofOverHom_zero_etale` is the adjunction transpose of `ofOverHom_zero_zariski`
along `ofOverEpsilon`. -/
theorem ofOverHom_zero_etale_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHom_zero_etale f0 =
      (modulePullbackHomEquiv.{u} (ofOverEpsilon X0)
          (((schemeToZariskiComplex X0.left).obj
              (Scheme.Hom.naiveCotangent f0.left)).X 0)
          (cotangentSpaceSheaf (ofOverMap f0))).symm
        (ofOverHom_zero_zariski f0) :=
  sorry

/-- Degreewise components of the comparison `(ε* NL_{X0/Y0}) ⟶ NL_{X/Y}`. -/
def ofOverHom_app {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) (n : ℤ) :
    (epsilonStarComplex f0).X n ⟶ (naiveCotangent (ofOverMap f0)).X n :=
  match n with
  | Int.negSucc 0 => ofOverHom_negOne f0
  | Int.ofNat 0 => ofOverHom_zero f0
  | _ => 0

/-- The degree `-1` component of `ofOverHom_app` is `ofOverHom_negOne`. -/
theorem ofOverHom_app_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHom_app f0 (-1) = ofOverHom_negOne f0 :=
  sorry

/-- The degree `0` component of `ofOverHom_app` is `ofOverHom_zero`. -/
theorem ofOverHom_app_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHom_app f0 0 = ofOverHom_zero f0 :=
  sorry

/-- The degreewise comparison maps commute with differentials. -/
theorem ofOverHom_app_comm {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    ofOverHom_app f0 i ≫ (naiveCotangent (ofOverMap f0)).d i j =
      (epsilonStarComplex f0).d i j ≫ ofOverHom_app f0 j :=
  sorry

/-- The canonical comparison `(ε* NL_{X0/Y0}) ⟶ NL_{X/Y}` of complexes of `𝒪_X`-modules. -/
def ofOverHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarComplex f0 ⟶ naiveCotangent (ofOverMap f0) where
  f n := ofOverHom_app f0 n
  comm' i j hij := ofOverHom_app_comm f0 i j hij

/-- The degree `-1` component of `ofOverHom` is the adjunction transpose of the `ε`-square
conormal comparison. -/
theorem ofOverHom_f_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom f0).f (-1) = ofOverHom_negOne f0 :=
  sorry

/-- The degree `0` component of `ofOverHom` is the adjunction transpose of the `ε`-square
presentation-differentials comparison. -/
theorem ofOverHom_f_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom f0).f 0 = ofOverHom_zero f0 :=
  sorry

/-- The degree `-1` and `0` components of `ofOverHom` unfold to opens-site transport,
the AffineComparison inverse, and the `ε`-square functoriality map. -/
theorem ofOverHom_spec {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom f0).f (-1) =
        ((modulePullbackCompIso (schemeEtaleRingedHom X0)
            (smallEtaleToZariski X0.left)).inv.app
            (((schemeToZariskiComplex X0.left).obj
                (Scheme.Hom.naiveCotangent f0.left)).X (-1))) ≫
          ofOverHom_negOne_etale f0 ∧
      (ofOverHom f0).f 0 =
        ((modulePullbackCompIso (schemeEtaleRingedHom X0)
            (smallEtaleToZariski X0.left)).inv.app
            (((schemeToZariskiComplex X0.left).obj
                (Scheme.Hom.naiveCotangent f0.left)).X 0)) ≫
          ofOverHom_zero_etale f0 :=
  sorry

/-- The canonical morphism `ε* NL_{X0/Y0} ⟶ NL_{X/Y}` in `D(𝒪_X)`. -/
def ofOverHomDerived {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    DerivedCategory.Q.obj (epsilonStarComplex f0) ⟶
      DerivedCategory.Q.obj (naiveCotangent (ofOverMap f0)) :=
  DerivedCategory.Q.map (ofOverHom f0)

/-- The derived comparison is the image of `ofOverHom` under `DerivedCategory.Q`. -/
theorem ofOverHomDerived_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ofOverHomDerived f0 = DerivedCategory.Q.map (ofOverHom f0) :=
  sorry

/-- The comparison `ε* NL_{X0/Y0} ⟶ NL_{X/Y}` is an isomorphism in `D(𝒪_X)`. -/
instance ofOverHomDerived_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIso (ofOverHomDerived f0) :=
  sorry

/-- The canonical identification `ε* NL_{X0/Y0} ≅ NL_{X/Y}` in `D(𝒪_X)`. -/
def ofOverHomIso_derived {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    DerivedCategory.Q.obj (epsilonStarComplex f0) ≅
      DerivedCategory.Q.obj (naiveCotangent (ofOverMap f0)) :=
  asIso (ofOverHomDerived f0)

/-- The forward map of `ofOverHomIso_derived` is `ofOverHomDerived`. -/
theorem ofOverHomIso_derived_hom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHomIso_derived f0).hom = ofOverHomDerived f0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
