/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap92.Lemma_92_26_2_Comparison
public import stacks_project.Chap92.«92_28_0_1_Transitivity»

/-!
# Comparison of cotangent complexes of representable algebraic spaces with schemes

For a morphism of schemes `f0 : X0 ⟶ Y0` over `S`, this module owns the morphism
`ε` of Stacks 75.4 from the small étale ringed site of `ofOver X0` to the small
Zariski ringed site of `X0.left`, the pulled complex `ε* L_{X0/Y0}` in
`D(𝒪_{ofOver X0})`, and the canonical comparison with `L_{ofOver X0 / ofOver Y0}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.Scheme.SiteRestriction
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable {S : Scheme.{u}}

/-- The morphism `ε` of Stacks 75.4 for a representable algebraic space, as the composite of
the identification of small étale sites with the restriction from the small étale site of
the representing scheme to its small Zariski site. -/
def epsilonHom (X0 : Over S) :
    RingedSite.Hom (ringedSite (ofOver X0)) (Scheme.Zariski.Small.ringedSite X0.left) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom X0) (smallEtaleToZariski X0.left)

/-- `epsilonHom` is the composite of `schemeEtaleRingedHom` with `smallEtaleToZariski`. -/
theorem epsilonHom_eq (X0 : Over S) :
    epsilonHom X0 =
      RingedSite.Hom.comp (schemeEtaleRingedHom X0) (smallEtaleToZariski X0.left) :=
  sorry

/-- The base of `epsilonHom` is the composite of the small-Zariski inclusion among étale
morphisms with the comparison from schemes étale over `X0.left` to the small étale site of
`ofOver X0`. -/
theorem epsilonHom_base (X0 : Over S) :
    (epsilonHom X0).base =
      smallZariskiToSmallEtale X0.left ⋙ schemeEtaleToSmallEtale X0 :=
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

/-- The base of `epsilonHom` is continuous for the small Zariski and small étale topologies. -/
instance epsilonHom_base_isContinuous (X0 : Over S) :
    (epsilonHom X0).base.IsContinuous
      X0.left.smallZariskiTopology (smallEtaleTopology (ofOver X0)) :=
  sorry

/-- The base of a small-Zariski ringed-site morphism is continuous. -/
instance zariskiRingedHom_base_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Zariski.Small.ringedHom f).base.IsContinuous
      Y.smallZariskiTopology X.smallZariskiTopology :=
  sorry

/-- Commutative-ring pushforward along `epsilonHom` admits a left adjoint. -/
instance epsilonHom_sheafPushforwardContinuous_commRing_isRightAdjoint (X0 : Over S) :
    ((epsilonHom X0).base.sheafPushforwardContinuous CommRingCat.{u}
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
  ((epsilonHom X0).base.sheafPullback CommRingCat.{u}
      X0.left.smallZariskiTopology
      (smallEtaleTopology (ofOver X0))).obj R

/-- Inverse image of a morphism of commutative-ring sheaves along `ε`. -/
def epsilonInverseImageMap (X0 : Over S)
    {R R' : Sheaf X0.left.smallZariskiTopology CommRingCat.{u}} (α : R ⟶ R') :
    epsilonInverseImage X0 R ⟶ epsilonInverseImage X0 R' :=
  ((epsilonHom X0).base.sheafPullback CommRingCat.{u}
      X0.left.smallZariskiTopology
      (smallEtaleTopology (ofOver X0))).map α

/-- Unfolding of `epsilonInverseImage` as sheaf pullback along the base of `epsilonHom`. -/
theorem epsilonInverseImage_eq (X0 : Over S)
    (R : Sheaf X0.left.smallZariskiTopology CommRingCat.{u}) :
    epsilonInverseImage X0 R =
      ((epsilonHom X0).base.sheafPullback CommRingCat.{u}
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
      ((epsilonHom X0).base.sheafPushforwardContinuous CommRingCat.{u}
        X0.left.smallZariskiTopology
        (smallEtaleTopology (ofOver X0))).obj
        (commStructureSheaf (ofOver X0)) :=
  InducedCategory.homMk
    { app := fun V ↦
        CommRingCat.ofHom ((epsilonHom X0).structureSheafMap.hom.app V).hom
      naturality := fun _ _ _ ↦ sorry }

/-- The inverse-image form `ε^♯ : ε⁻¹ 𝒪_{X0} ⟶ 𝒪_X` on the small étale site of
`ofOver X0`. -/
def epsilonSharpUnlifted (X0 : Over S) :
    epsilonInverseImage X0 (zariskiCommStructureSheaf X0.left) ⟶
      commStructureSheaf (ofOver X0) :=
  (((epsilonHom X0).base.sheafAdjunctionContinuous CommRingCat.{u}
        X0.left.smallZariskiTopology
        (smallEtaleTopology (ofOver X0))).homEquiv
      (zariskiCommStructureSheaf X0.left) (commStructureSheaf (ofOver X0))).symm
    (epsilonStructureSheafMapComm X0)

/-- Unfolding of `epsilonSharpUnlifted` as the adjunct of `epsilonStructureSheafMapComm`. -/
theorem epsilonSharpUnlifted_eq (X0 : Over S) :
    epsilonSharpUnlifted X0 =
      (((epsilonHom X0).base.sheafAdjunctionContinuous CommRingCat.{u}
            X0.left.smallZariskiTopology
            (smallEtaleTopology (ofOver X0))).homEquiv
          (zariskiCommStructureSheaf X0.left)
          (commStructureSheaf (ofOver X0))).symm
        (epsilonStructureSheafMapComm X0) :=
  sorry

/-- Universe-lifted inverse image `ε⁻¹ 𝒪_{X0}` on the small étale site of `ofOver X0`. -/
abbrev epsilonInverseImageLift (X0 : Over S) :
    Sheaf (smallEtaleTopology (ofOver X0)) CommRingCat.{u + 1} :=
  liftSheafObj (ofOver X0) (epsilonInverseImage X0 (zariskiCommStructureSheaf X0.left))

/-- Identification of the universe lift of `commStructureSheaf` with `commStructureSheafLift`. -/
def liftCommStructureSheafMap (X : AlgebraicSpace S) :
    liftSheafObj X (commStructureSheaf X) ⟶ commStructureSheafLift X :=
  ObjectProperty.homMk (𝟙 (liftPresheaf X (commStructureSheaf X).obj))

/-- `liftCommStructureSheafMap` is the identity on the underlying lifted presheaf. -/
theorem liftCommStructureSheafMap_eq (X : AlgebraicSpace S) :
    liftCommStructureSheafMap X =
      ObjectProperty.homMk (𝟙 (liftPresheaf X (commStructureSheaf X).obj)) :=
  sorry

/-- The lifted structure map `ε^♯ : ε⁻¹ 𝒪_{X0} ⟶ 𝒪_X`. -/
def epsilonSharpLift (X0 : Over S) :
    epsilonInverseImageLift X0 ⟶ commStructureSheafLift (ofOver X0) :=
  liftSheafMap (ofOver X0) (epsilonSharpUnlifted X0) ≫
    liftCommStructureSheafMap (ofOver X0)

/-- Unfolding of `epsilonSharpLift` as the universe lift of `epsilonSharpUnlifted`. -/
theorem epsilonSharpLift_eq (X0 : Over S) :
    epsilonSharpLift X0 =
      liftSheafMap (ofOver X0) (epsilonSharpUnlifted X0) ≫
        liftCommStructureSheafMap (ofOver X0) :=
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
def epsilonInverseImageSchemeAlgebraUnlifted {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImage X0 (schemeInverseImage f0.left) ⟶
      epsilonInverseImage X0 (zariskiCommStructureSheaf X0.left) :=
  epsilonInverseImageMap X0 (schemeAlgebra f0.left)

/-- Unfolding of `epsilonInverseImageSchemeAlgebraUnlifted` as `epsilonInverseImageMap` of
`schemeAlgebra`. -/
theorem epsilonInverseImageSchemeAlgebraUnlifted_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageSchemeAlgebraUnlifted f0 =
      epsilonInverseImageMap X0 (schemeAlgebra f0.left) :=
  sorry

/-- The lifted algebra map `ε⁻¹ f0^♯` on the `ε_X⁻¹` presentation. -/
def epsilonInverseImageSchemeAlgebra {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    liftSheafObj (ofOver X0) (epsilonInverseImage X0 (schemeInverseImage f0.left)) ⟶
      epsilonInverseImageLift X0 :=
  liftSheafMap (ofOver X0) (epsilonInverseImageSchemeAlgebraUnlifted f0)

/-- Unfolding of `epsilonInverseImageSchemeAlgebra` as the universe lift of
`epsilonInverseImageSchemeAlgebraUnlifted`. -/
theorem epsilonInverseImageSchemeAlgebra_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageSchemeAlgebra f0 =
      liftSheafMap (ofOver X0) (epsilonInverseImageSchemeAlgebraUnlifted f0) :=
  sorry

/-- The cochain complex `ε⁻¹ L_{X0/Y0}` of modules over `ε⁻¹ 𝒪_{X0}`. -/
def epsilonInverseImageSchemeCotangentCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    CochainComplex
      (SheafOfModules.{u + 1} (ringOf (epsilonInverseImageLift X0))) ℤ :=
  cotangentCochainObj (epsilonInverseImageSchemeAlgebra f0)

/-- Unfolding of `epsilonInverseImageSchemeCotangentCochain` as the sheaf-level cotangent of
`ε⁻¹ f0^♯`. -/
theorem epsilonInverseImageSchemeCotangentCochain_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageSchemeCotangentCochain f0 =
      cotangentCochainObj (epsilonInverseImageSchemeAlgebra f0) :=
  sorry

/-- Inverse image of `ε_Y⁻¹ 𝒪_{Y0}` along `ofOverMap f0`. -/
def pulledEpsilonInverseImage {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    Sheaf (smallEtaleTopology (ofOver X0)) CommRingCat.{u} :=
  commSheafInverseImageObj (ofOverMap f0)
    (epsilonInverseImage Y0 (zariskiCommStructureSheaf Y0.left))

/-- Compatibility map `f⁻¹(ε_Y⁻¹ 𝒪_{Y0}) ⟶ f_small⁻¹ 𝒪_Y` obtained by inverse image of
`ε_Y^♯`. -/
def pulledEpsilonSharp {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    pulledEpsilonInverseImage f0 ⟶ commInverseImageStructureSheaf (ofOverMap f0) :=
  commSheafInverseImageMap (ofOverMap f0) (epsilonSharpUnlifted Y0)

/-- Unfolding of `pulledEpsilonSharp` as inverse image of `epsilonSharpUnlifted`. -/
theorem pulledEpsilonSharp_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    pulledEpsilonSharp f0 =
      commSheafInverseImageMap (ofOverMap f0) (epsilonSharpUnlifted Y0) :=
  sorry

/-- Universe-lifted inverse image `ε⁻¹ f0⁻¹ 𝒪_{Y0}`, presented via the étale path of the
commutative square of sites. -/
abbrev epsilonInverseImageSchemeLift {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    Sheaf (smallEtaleTopology (ofOver X0)) CommRingCat.{u + 1} :=
  liftSheafObj (ofOver X0) (pulledEpsilonInverseImage f0)

/-- Compatibility map `ε⁻¹ f0⁻¹ 𝒪_{Y0} ⟶ f_small⁻¹ 𝒪_Y`. -/
def epsilonInverseImageBase {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageSchemeLift f0 ⟶ inverseImageLift (ofOverMap f0) :=
  liftSheafMap (ofOver X0) (pulledEpsilonSharp f0)

/-- Unfolding of `epsilonInverseImageBase` as the universe lift of `pulledEpsilonSharp`. -/
theorem epsilonInverseImageBase_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageBase f0 =
      liftSheafMap (ofOver X0) (pulledEpsilonSharp f0) :=
  sorry

/-- The composite algebra map `ε⁻¹ f0^♯ ≫ ε^♯`, as `w ≫ f_small^♯`. -/
abbrev epsilonCompositeStructureMap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageSchemeLift f0 ⟶ commStructureSheafLift (ofOver X0) :=
  epsilonInverseImageBase f0 ≫ structureMapLift (ofOverMap f0)

/-- The cochain complex `ε* L_{X0/Y0}` of lifted `𝒪_X`-modules. -/
def epsilonStarSchemeCotangentCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    CochainComplex (CommModules (ofOver X0)) ℤ :=
  cotangentCochainObj (epsilonCompositeStructureMap f0)

/-- Unfolding of `epsilonStarSchemeCotangentCochain` as the sheaf-level cotangent of
`w ≫ f_small^♯`. -/
theorem epsilonStarSchemeCotangentCochain_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangentCochain f0 =
      cotangentCochainObj (epsilonCompositeStructureMap f0) :=
  sorry

/-- The object `ε* L_{X0/Y0}` in `D(𝒪_X)`. -/
def epsilonStarSchemeCotangent {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    DerivedCategory (CommModules (ofOver X0)) :=
  DerivedCategory.Q.obj (epsilonStarSchemeCotangentCochain f0)

/-- Unfolding of `epsilonStarSchemeCotangent` as `DerivedCategory.Q` of
`epsilonStarSchemeCotangentCochain`. -/
theorem epsilonStarSchemeCotangent_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangent f0 =
      DerivedCategory.Q.obj (epsilonStarSchemeCotangentCochain f0) :=
  sorry

/-- The algebra square relating `ε⁻¹ f0^♯` to `f_small^♯` commutes. -/
theorem epsilonInverseImageBase_w {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonInverseImageBase f0 ≫ structureMapLift (ofOverMap f0) =
      epsilonCompositeStructureMap f0 ≫ 𝟙 (commStructureSheafLift (ofOver X0)) :=
  sorry

/-- Degreewise map of simplicial cotangent modules induced by `epsilonInverseImageBase`. -/
def epsilonStarSchemeCompareSimplicial {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (epsilonInverseImageSchemeLift f0)
        (Under.mk (epsilonCompositeStructureMap f0))).obj n ⟶
      (simplicialModule (inverseImageLift (ofOverMap f0))
        (Under.mk (structureMapLift (ofOverMap f0)))).obj n :=
  baseChangeSimplicialHom (epsilonInverseImageBase f0)
    (epsilonCompositeStructureMap f0) (structureMapLift (ofOverMap f0))
    (epsilonInverseImageBase_w f0) n

/-- The cochain map `L(ε⁻¹ f0^♯ ≫ ε^♯) ⟶ L_{X/Y}` induced by the algebra square. -/
def epsilonCompositeCompareCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    cotangentCochainObj (epsilonCompositeStructureMap f0) ⟶
      cotangentCochain (ofOverMap f0) where
  f i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendXIso
            ((alternatingFaceMapComplex
                (SheafOfModules.{u + 1}
                  (ringOf (commStructureSheafLift (ofOver X0))))).obj
              (simplicialModule (epsilonInverseImageSchemeLift f0)
                (Under.mk (epsilonCompositeStructureMap f0))))
            embeddingDownNat
            (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
          epsilonStarSchemeCompareSimplicial f0 (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules.{u + 1}
                    (ringOf (commStructureSheafLift (ofOver X0))))).obj
                (simplicialModule (inverseImageLift (ofOverMap f0))
                  (Under.mk (structureMapLift (ofOverMap f0)))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0
  comm' := sorry

/-- The canonical cochain comparison `ε* L_{X0/Y0} ⟶ L_{X/Y}`. -/
def epsilonStarSchemeCompareCochain {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangentCochain f0 ⟶ cotangentCochain (ofOverMap f0) :=
  epsilonCompositeCompareCochain f0

/-- Unfolding of `epsilonStarSchemeCompareCochain` as the algebra-square comparison. -/
theorem epsilonStarSchemeCompareCochain_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCompareCochain f0 = epsilonCompositeCompareCochain f0 :=
  sorry

/-- The canonical comparison `ε* L_{X0/Y0} ⟶ L_{X/Y}` in `D(𝒪_X)`. -/
def epsilonStarSchemeCompare {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangent f0 ⟶ cotangent (ofOverMap f0) :=
  DerivedCategory.Q.map (epsilonStarSchemeCompareCochain f0)

/-- Unfolding of `epsilonStarSchemeCompare` as `DerivedCategory.Q.map` of
`epsilonStarSchemeCompareCochain`. -/
theorem epsilonStarSchemeCompare_eq {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCompare f0 =
      DerivedCategory.Q.map (epsilonStarSchemeCompareCochain f0) :=
  sorry

/-- The comparison `ε* L_{X0/Y0} ⟶ L_{X/Y}` is an isomorphism in `D(𝒪_X)`. -/
instance epsilonStarSchemeCompare_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIso (epsilonStarSchemeCompare f0) :=
  sorry

/-- The canonical identification `ε* L_{X0/Y0} ≅ L_{X/Y}` in `D(𝒪_X)`. -/
def epsilonStarSchemeCompareIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarSchemeCotangent f0 ≅ cotangent (ofOverMap f0) :=
  asIso (epsilonStarSchemeCompare f0)

/-- The forward map of `epsilonStarSchemeCompareIso` is `epsilonStarSchemeCompare`. -/
theorem epsilonStarSchemeCompareIso_hom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarSchemeCompareIso f0).hom = epsilonStarSchemeCompare f0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
