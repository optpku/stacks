/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Map
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import stacks_project.Chap91.Lemma_91_13_1_Diagram

/-!
# Canonical Ext¹ obstruction of a relative first-order thickening diagram

A relative diagram of first-order thickenings of sheaves on a site determines a canonical
class in `Ext⁽1⁾(Lg^* NL(f₁), 𝒢₂)` by comparing front and back lifts of a polynomial
presentation of `NL(f₁)` on the fiber-product generator sheaf `𝒪'₁ ×_{𝒪₂} 𝒪'₂`. Vanishing
of the class is equivalent to existence of a fitting map, and the fiber is a torsor under
`Hom(Ω(f₁), g_* 𝒢₂)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite RelativeDerivation
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{u}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [IsFirstOrderThickening πO1] [IsFirstOrderThickening πB1]
variable [IsFirstOrderThickening πO2] [IsFirstOrderThickening πB2]

/-- The derived-category quotient of cochain complexes of `𝒪`-modules. -/
abbrev moduleQ (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J O) ℤ ⥤
      DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O) :=
  DerivedCategory.Q

/-- `moduleQ O` is the derived-category quotient of cochain complexes of `𝒪`-modules. -/
theorem moduleQ_eq (O : Sheaf J CommRingCat.{u}) :
    moduleQ O = DerivedCategory.Q := sorry

/-- Same-site module pullback along `α` admits a total left derived functor. -/
instance instModulePullbackHasLeftDerived {O O' : Sheaf J CommRingCat.{u}} (α : O ⟶ O') :
    (Functor.Homotopy.toDerived ((sameSiteHom α).modulePullback)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (RingedSite.ofCommRingSheaf J O).ModuleCat
        (ComplexShape.up ℤ)) := sorry

/-- The fiber-product ring sheaf `𝒪'₁ ×_{𝒪₂} 𝒪'₂`. -/
def generatorRingSheaf (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Sheaf J CommRingCat.{u} :=
  Limits.pullback (πO1 ≫ D.g) πO2

/-- The underlying sheaf of sets of the fiber-product generator ring sheaf. -/
def generatorSheaf (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Sheaf J (Type u) :=
  (sheafForget J).obj (generatorRingSheaf D)

/-- The assignment of fiber-product generators to `𝒪₁` via the front projection. -/
def generatorAssign (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    generatorSheaf D ⟶ FreeAlgebra.Presentation.generators (Under.mk D.f1) :=
  (sheafForget J).map (Limits.pullback.fst (πO1 ≫ D.g) πO2 ≫ πO1)

/-- Front generator assignment `ℰ ⟶ 𝒪'₁`. -/
def generatorFrontAssign (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    generatorSheaf D ⟶ (sheafForget J).obj O1' :=
  (sheafForget J).map (Limits.pullback.fst (πO1 ≫ D.g) πO2)

/-- Back generator assignment `ℰ ⟶ 𝒪'₂`. -/
def generatorBackAssign (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    generatorSheaf D ⟶ (sheafForget J).obj O2' :=
  (sheafForget J).map (Limits.pullback.snd (πO1 ≫ D.g) πO2)

/-- Front evaluation `a : 𝒪_{B'₁}[ℰ] ⟶ 𝒪'₁`. -/
def evalFront (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ O1' :=
  (FreeAlgebra.evaluation (Under.mk D.f1') (generatorSheaf D) (generatorFrontAssign D)).right

/-- Back evaluation `b : 𝒪_{B'₁}[ℰ] ⟶ 𝒪'₂`. -/
def evalBack (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ O2' :=
  (FreeAlgebra.evaluation (Under.mk (D.t' ≫ D.f2')) (generatorSheaf D)
    (generatorBackAssign D)).right

/-- Evaluation of the `𝒪_{B₁}`-polynomial algebra on fiber-product generators to `𝒪₁`. -/
def evalToO1 (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1 [generatorSheaf D] ⟶ O1 :=
  (FreeAlgebra.evaluation (Under.mk D.f1) (generatorSheaf D) (generatorAssign D)).right

/-- Evaluation of the `𝒪_{B'₁}`-polynomial algebra on fiber-product generators to `𝒪₁`. -/
def evalToO1FromS' (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ O1 :=
  (FreeAlgebra.evaluation (Under.mk (D.f1' ≫ πO1)) (generatorSheaf D)
    (generatorAssign D)).right

/-- The two-term naive cotangent complex of the fiber-product presentation of `𝒪₁` over `𝒪_{B₁}`. -/
def generatorCotangent (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CochainComplex (SheafOfModules (ringSheaf J O1)) ℤ :=
  Presentation.ofGenerators (generatorSheaf D) (generatorAssign D)

/-- The coefficient map `𝒪_{B'₁}[ℰ] ⟶ 𝒪_{B₁}[ℰ]` induced by `π_{B₁}`. -/
def freeAlgebraS'toS (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ OB1 [generatorSheaf D] :=
  (FreeAlgebra.evaluation
      (Under.mk (πB1 ≫ FreeAlgebra.base OB1 (generatorSheaf D)))
      (generatorSheaf D) (FreeAlgebra.generator OB1 (generatorSheaf D))).right

/-- Presentation morphism from the `𝒪_{B'₁}`-polynomial presentation to the `𝒪_{B₁}`-presentation. -/
def s'toSPresentationHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Presentation.Hom (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)
      (FreeAlgebra.base OB1 (generatorSheaf D)) (evalToO1 D) where
  base := πB1
  middle := freeAlgebraS'toS D
  target := 𝟙 O1
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- The `𝒪_{B'₁}`-algebra presentation of `𝒪₁` on the fiber-product generators. -/
def generatorCotangentS' (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CochainComplex (SheafOfModules (ringSheaf J O1)) ℤ :=
  Presentation.complex (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)

/-- The comparison `I'/I'² ⟶ I/I²` of polynomial conormal sheaves. -/
def generatorConormalComparison (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ (generatorCotangent D).X (-1) :=
  ((extendComplexIdIso O1).inv.app (generatorCotangentS' D) ≫
    Presentation.Hom.map (s'toSPresentationHom D)).f (-1)

/-- The comparison `I'/I'² ⟶ I/I²` is an epimorphism. -/
instance generatorConormalComparison_epi (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Epi (generatorConormalComparison D) := sorry

/-- Presentation morphism from the `𝒪_{B'₁}`-polynomial presentation to the front thickening. -/
def frontPresentationHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Presentation.Hom (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)
      (𝟙 O1') πO1 where
  base := D.f1'
  middle := evalFront D
  target := 𝟙 O1
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- Front restriction `a|_{I'} : I'/I'² ⟶ 𝒢₁`. -/
def conormalToFrontKernel (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ conormalSource πO1 :=
  ((extendComplexIdIso O1).inv.app (generatorCotangentS' D) ≫
    Presentation.Hom.map (frontPresentationHom D)).f (-1)

/-- Presentation morphism from the `𝒪_{B'₁}`-polynomial presentation to the back thickening. -/
def backPresentationHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Presentation.Hom (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)
      (𝟙 O2') πO2 where
  base := D.t' ≫ D.f2'
  middle := evalBack D
  target := D.g
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- Back restriction `b|_{I'} : I'/I'² ⟶ g_* 𝒢₂` of the polynomial evaluation. -/
def conormalToBackKernel (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ (restrictionAlong D.g).obj (ideal πO2) :=
  ((extendRestrictAdj D.g).homEquiv
      ((generatorCotangentS' D).X (-1)) (ideal πO2))
    ((Presentation.Hom.map (backPresentationHom D)).f (-1) ≫
      SquareZeroExtension.conormalToTarget πO2
        (inferInstance : IsFirstOrderThickening πO2).isSquareZero)

/-- The obstruction representative on `I'/I'²`, comparing back and front generator lifts. -/
def conormalHomOverS' (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ (restrictionAlong D.g).obj (ideal πO2) :=
  conormalToBackKernel D -
    conormalToFrontKernel D ≫
      SquareZeroExtension.conormalToTarget πO1
        (inferInstance : IsFirstOrderThickening πO1).isSquareZero ≫ D.ν

/-- Incoming kernel of `I'/I'² ⟶ I/I²` is annihilated by the `𝒪_{B'₁}`-obstruction representative. -/
theorem generatorConormalComparison_kernel_comp (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    kernel.ι (generatorConormalComparison D) ≫ conormalHomOverS' D = 0 := sorry

/-- The obstruction representative `ξ : I/I² ⟶ g_* 𝒢₂` obtained by comparing front and back
generator lifts: `ξ = b|_{I'} - ν ∘ a|_{I'}`. -/
def conormalHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangent D).X (-1) ⟶ (restrictionAlong D.g).obj (ideal πO2) :=
  CategoryTheory.Abelian.epiDesc (generatorConormalComparison D) (conormalHomOverS' D)
    (generatorConormalComparison_kernel_comp D)

/-- `conormalHom` compares the back and front evaluations of a lifted cotangent class. -/
theorem conormalHom_apply (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    conormalHom D =
      CategoryTheory.Abelian.epiDesc (generatorConormalComparison D) (conormalHomOverS' D)
        (generatorConormalComparison_kernel_comp D) := sorry

/-- The adjunct of `conormalHom`, as an `𝒪₂`-linear map `g^* (I/I²) ⟶ 𝒢₂`. -/
def conormalHomPull (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (extendAlong D.g).obj ((generatorCotangent D).X (-1)) ⟶ ideal πO2 :=
  ((extendRestrictAdj D.g).homEquiv
    ((generatorCotangent D).X (-1)) (ideal πO2)).symm (conormalHom D)

/-- Degreewise inverse image of the fiber-product presentation model along `g`. -/
def pulledGeneratorCotangent (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CochainComplex (SheafOfModules (ringSheaf J O2)) ℤ :=
  ((extendAlong D.g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (generatorCotangent D)

/-- Incoming differentials into degree `-1` of the pulled presentation vanish after composing
with the adjunct of `conormalHom`. -/
theorem pulledGeneratorCotangent_d_comp (D : RelativeDiagram πO1 πB1 πO2 πB2)
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel k (-1)) :
    (pulledGeneratorCotangent D).d k (-1) ≫ conormalHomPull D = 0 := sorry

/-- The morphism of complexes `g^* NL(α) ⟶ 𝒢₂[-1]` associated to `conormalHom`. -/
def conormalHomToSingle (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    pulledGeneratorCotangent D ⟶
      (CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) (-1 : ℤ)).obj
        (ideal πO2) :=
  HomologicalComplex.mkHomToSingle (conormalHomPull D) (pulledGeneratorCotangent_d_comp D)

/-- The derived class of `conormalHom` in `Ext⁽1⁾(g^* NL(α), 𝒢₂)`. -/
def mapObstructionUnderived (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Ext⁽(1 : ℤ)⁾((moduleQ O2).obj (pulledGeneratorCotangent D),
      (moduleQ O2).obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).obj
          (ideal πO2))) :=
  (moduleQ O2).map (conormalHomToSingle D) ≫
    ((DerivedCategory.singleFunctors
        (ringedSiteModuleCategory.{u, u, u, u} J O2)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app (ideal πO2)

/-- Derived-to-underived comparison `Lg^* NL(α) ⟶ g^* NL(α)` on the fiber-product presentation. -/
def mapObstructionCounit (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (SameSite.pullbackDerived D.g).obj ((moduleQ O1).obj (generatorCotangent D)) ⟶
      (moduleQ O2).obj (pulledGeneratorCotangent D) :=
  (Functor.LeftDerived.Homotopy.cochainCounit ((sameSiteHom D.g).modulePullback)).app (generatorCotangent D)

/-- The generator assignment `ℰ ⟶ 𝒪₁` is locally surjective because `π_{𝒪₁}` is a thickening. -/
instance generatorAssign_isLocallySurjective (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Sheaf.IsLocallySurjective (generatorAssign D) := sorry

/-- Derived identification of the fiber-product presentation with `NL(f₁)`. -/
def generatorDerivedIso (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (moduleQ O1).obj (generatorCotangent D) ≅
      (moduleQ O1).obj (NaiveCotangent.obj OB1 (Under.mk D.f1)) :=
  Presentation.ofGeneratorsIso (generatorSheaf D) (generatorAssign D)

/-- The canonical class in `Ext⁽1⁾(Lg^* NL(f₁), 𝒢₂)` attached to a relative diagram. -/
def mapObstruction (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Ext⁽(1 : ℤ)⁾(
      (SameSite.pullbackDerived D.g).obj
        ((moduleQ O1).obj (NaiveCotangent.obj OB1 (Under.mk D.f1))),
      (moduleQ O2).obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).obj
          (ideal πO2))) :=
  (SameSite.pullbackDerived D.g).map (generatorDerivedIso D).inv ≫
    mapObstructionCounit D ≫ mapObstructionUnderived D

/-- `mapObstruction` is the derived class of `conormalHom`, compared with `Lg^* NL(f₁)` and `𝒢₂`. -/
theorem mapObstruction_spec (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    mapObstruction D =
      (SameSite.pullbackDerived D.g).map (generatorDerivedIso D).inv ≫
        mapObstructionCounit D ≫ mapObstructionUnderived D := sorry

variable {D : RelativeDiagram πO1 πB1 πO2 πB2}

/-- The adjunction identification `Hom(Ω(f₁), g_* 𝒢₂) ≃ Hom(g^* Ω(f₁), 𝒢₂)`. -/
def homOmegaPushforwardEquiv :
    (Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) ≃
      ((extendAlong D.g).obj Ω(D.f1) ⟶ ideal πO2) :=
  ((extendRestrictAdj D.g).homEquiv Ω(D.f1) (ideal πO2)).symm

/-- `homOmegaPushforwardEquiv` is the inverse of the extension-restriction Hom-equivalence. -/
theorem homOmegaPushforwardEquiv_apply (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    homOmegaPushforwardEquiv α =
      ((extendRestrictAdj D.g).homEquiv Ω(D.f1) (ideal πO2)).symm α := sorry

/-- The degree-zero single functor on `𝒪₁`-modules used by `NaiveCotangent.differentialsComplex`. -/
abbrev homOmegaSingleFunctor :
    SheafOfModules (ringSheaf J O1) ⥤
      CochainComplex (SheafOfModules (ringSheaf J O1)) ℤ :=
  HomologicalComplex.single (SheafOfModules (ringSheaf J O1)) (ComplexShape.up ℤ) 0

/-- `homOmegaSingleFunctor` is degree-zero `HomologicalComplex.single` on `𝒪₁`-modules. -/
theorem homOmegaSingleFunctor_eq :
    homOmegaSingleFunctor =
      HomologicalComplex.single (SheafOfModules (ringSheaf J O1)) (ComplexShape.up ℤ) 0 := sorry

/-- Degree-zero single of a map `Ω(f₁) ⟶ g_* 𝒢₂`, as a map of the same single complexes used by
`NaiveCotangent.differentialsComplex`. -/
def homOmegaSingle (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    NaiveCotangent.differentialsComplex OB1 (Under.mk D.f1) ⟶
      homOmegaSingleFunctor.obj ((restrictionAlong D.g).obj (ideal πO2)) :=
  homOmegaSingleFunctor.map α

/-- `homOmegaSingle` is the degree-zero single of the given map of `𝒪₁`-modules. -/
theorem homOmegaSingle_apply (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    homOmegaSingle α = homOmegaSingleFunctor.map α := sorry

/-- Derived-to-underived comparison `Lg^* (g_* 𝒢₂)[0] ⟶ 𝒢₂[0]`. -/
def homOmegaCounit :
    (SameSite.pullbackDerived D.g).obj
      ((moduleQ O1).obj
        (homOmegaSingleFunctor.obj ((restrictionAlong D.g).obj (ideal πO2)))) ⟶
    (moduleQ O2).obj
      ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).obj (ideal πO2)) :=
  (Functor.LeftDerived.Homotopy.cochainCounit ((sameSiteHom D.g).modulePullback)).app
      (homOmegaSingleFunctor.obj ((restrictionAlong D.g).obj (ideal πO2))) ≫
    (moduleQ O2).map
      ((HomologicalComplex.singleMapHomologicalComplex
          ((sameSiteHom D.g).modulePullback) (ComplexShape.up ℤ) (0 : ℤ)).hom.app
        ((restrictionAlong D.g).obj (ideal πO2)) ≫
        (CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).map
          ((pullbackExtendIso D.g).hom.app ((restrictionAlong D.g).obj (ideal πO2)) ≫
            (extendRestrictAdj D.g).counit.app (ideal πO2)))

/-- The unshifted morphism in `D(𝒪₂)` associated to a map `Ω(f₁) ⟶ g_* 𝒢₂`. -/
def homOmegaDerived (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    (SameSite.pullbackDerived D.g).obj
        ((moduleQ O1).obj (NaiveCotangent.obj OB1 (Under.mk D.f1))) ⟶
      (moduleQ O2).obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).obj
          (ideal πO2)) :=
  (SameSite.pullbackDerived D.g).map
      ((moduleQ O1).map
        (NaiveCotangent.augmentation OB1 (Under.mk D.f1) ≫ homOmegaSingle α)) ≫
    homOmegaCounit

/-- The forward identification of the acting group with `Ext⁽0⁾(Lg^* NL(f₁), 𝒢₂)`. -/
def homOmegaExtZero (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    Ext⁽(0 : ℤ)⁾(
      (SameSite.pullbackDerived D.g).obj
        ((moduleQ O1).obj (NaiveCotangent.obj OB1 (Under.mk D.f1))),
      (moduleQ O2).obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).obj
          (ideal πO2))) :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α)

/-- `homOmegaExtZero` sends a map `Ω(f₁) ⟶ g_* 𝒢₂` to the corresponding degree-zero Ext class. -/
theorem homOmegaExtZero_apply (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    homOmegaExtZero α =
      (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α) := sorry

/-- The map `Hom(Ω(f₁), g_* 𝒢₂) → Ext⁽0⁾(Lg^* NL(f₁), 𝒢₂)` is an isomorphism. -/
theorem homOmegaExtZero_bijective :
    Function.Bijective
      (fun α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2) ↦ homOmegaExtZero α) :=
  sorry

/-- The kernel-ideal section of `π_{𝒪₂}` obtained by evaluating `α ∘ d(f₁)` on `π_{𝒪₁}` of a
section of `𝒪'₁`. -/
def perturbKernelSection (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (U : Cᵒᵖ) (x : O1'.obj.obj U) :
    (KernelIdeal.sheaf πO2).val.obj U :=
  ((inferInstance : IsFirstOrderThickening πO2).isSquareZero.targetModuleForgetIso
      inferInstance).hom.hom.app U
    (α.val.app U ((relativeDifferential D.f1).d (πO1.hom.app U x)))

/-- Square-zero inclusion of the perturbation section into `𝒪'₂`. -/
def perturbContribution (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (U : Cᵒᵖ) (x : O1'.obj.obj U) :
    O2'.obj.obj U :=
  KernelIdeal.ιApp πO2 U (perturbKernelSection α U x)

/-- The component ring homomorphism of a perturbed structure-sheaf map. -/
def perturbRingHom (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) (U : Cᵒᵖ) :
    O1'.obj.obj U →+* O2'.obj.obj U where
  toFun x := φ.hom.hom.app U x + perturbContribution α U x
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The structure-sheaf map of `φ`, modified by the square-zero inclusion of `α ∘ d(f₁)` into
`Ker(π_{𝒪₂})`. -/
def perturbHom (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) : O1' ⟶ O2' :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (perturbRingHom α φ U)
      naturality {U V} i := sorry }

/-- The action of `Hom(Ω(f₁), g_* 𝒢₂)` on fitting maps, adding `α ∘ d(f₁)` through the
square-zero kernel of `π_{𝒪₂}`. -/
def perturb (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) : FittingMap D :=
  FittingMap.of (perturbHom α φ) sorry sorry sorry

/-- `perturb` does not change the composite of the filling morphism with `π_{𝒪₂}`. -/
theorem perturb_hom (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) :
    (perturb α φ).hom ≫ πO2 = φ.hom ≫ πO2 := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
