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
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FittingMap

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

set_option backward.privateInPublic true

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable [UnivLE.{max u v, w}]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{w}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [hπO1 : IsFirstOrderThickening πO1] [hπB1 : IsFirstOrderThickening πB1]
variable [hπO2 : IsFirstOrderThickening πO2] [hπB2 : IsFirstOrderThickening πB2]

namespace MapObstructionConstruction

/-- The fiber-product ring sheaf `𝒪'₁ ×_{𝒪₂} 𝒪'₂`. -/
private def generatorRingSheaf (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Sheaf J CommRingCat.{w} :=
  Limits.pullback (πO1 ≫ D.g) πO2

/-- The underlying sheaf of sets of the fiber-product generator ring sheaf. -/
private def generatorSheaf (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Sheaf J (Type w) :=
  (sheafForget J).obj (generatorRingSheaf D)

/-- The assignment of fiber-product generators to `𝒪₁` via the front projection. -/
private def generatorAssign (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    generatorSheaf D ⟶ FreeAlgebra.Presentation.generators (Under.mk D.f1) :=
  (sheafForget J).map (Limits.pullback.fst (πO1 ≫ D.g) πO2 ≫ πO1)

/-- Front generator assignment `ℰ ⟶ 𝒪'₁`. -/
private def generatorFrontAssign (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    generatorSheaf D ⟶ (sheafForget J).obj O1' :=
  (sheafForget J).map (Limits.pullback.fst (πO1 ≫ D.g) πO2)

/-- Back generator assignment `ℰ ⟶ 𝒪'₂`. -/
private def generatorBackAssign (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    generatorSheaf D ⟶ (sheafForget J).obj O2' :=
  (sheafForget J).map (Limits.pullback.snd (πO1 ≫ D.g) πO2)

/-- Front evaluation `a : 𝒪_{B'₁}[ℰ] ⟶ 𝒪'₁`. -/
private def evalFront (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ O1' :=
  (FreeAlgebra.evaluation (Under.mk D.f1') (generatorSheaf D) (generatorFrontAssign D)).right

/-- Back evaluation `b : 𝒪_{B'₁}[ℰ] ⟶ 𝒪'₂`. -/
private def evalBack (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ O2' :=
  (FreeAlgebra.evaluation (Under.mk (D.t' ≫ D.f2')) (generatorSheaf D)
    (generatorBackAssign D)).right

/-- Evaluation of the `𝒪_{B₁}`-polynomial algebra on fiber-product generators to `𝒪₁`. -/
private def evalToO1 (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1 [generatorSheaf D] ⟶ O1 :=
  (FreeAlgebra.evaluation (Under.mk D.f1) (generatorSheaf D) (generatorAssign D)).right

/-- Evaluation of the `𝒪_{B'₁}`-polynomial algebra on fiber-product generators to `𝒪₁`. -/
private def evalToO1FromS' (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ O1 :=
  (FreeAlgebra.evaluation (Under.mk (D.f1' ≫ πO1)) (generatorSheaf D)
    (generatorAssign D)).right

/-- The two-term naive cotangent complex of the fiber-product presentation of `𝒪₁` over `𝒪_{B₁}`. -/
private def generatorCotangent (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CochainComplex (SheafOfModules (ringSheaf J O1)) ℤ :=
  Presentation.ofGenerators (generatorSheaf D) (generatorAssign D)

/-- The coefficient map `𝒪_{B'₁}[ℰ] ⟶ 𝒪_{B₁}[ℰ]` induced by `π_{B₁}`. -/
private def freeAlgebraS'toS (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    OB1' [generatorSheaf D] ⟶ OB1 [generatorSheaf D] :=
  (FreeAlgebra.evaluation
      (Under.mk (πB1 ≫ FreeAlgebra.base OB1 (generatorSheaf D)))
      (generatorSheaf D) (FreeAlgebra.generator OB1 (generatorSheaf D))).right

/-- The coefficient, evaluation, and quotient maps form commuting presentation squares. -/
private theorem s'toSPresentationHom_laws (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq (πB1) (FreeAlgebra.base OB1' (generatorSheaf D)) (FreeAlgebra.base OB1 (generatorSheaf D)) (freeAlgebraS'toS D) ∧
      CommSq (freeAlgebraS'toS D) (evalToO1FromS' D) (evalToO1 D) (𝟙 O1) := sorry

private def s'toSPresentationHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Presentation.Hom (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)
      (FreeAlgebra.base OB1 (generatorSheaf D)) (evalToO1 D) where
  base := πB1
  middle := freeAlgebraS'toS D
  target := 𝟙 O1
  baseSq := (s'toSPresentationHom_laws D).1
  targetSq := (s'toSPresentationHom_laws D).2

/-- The `𝒪_{B'₁}`-algebra presentation of `𝒪₁` on the fiber-product generators. -/
private def generatorCotangentS' (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CochainComplex (SheafOfModules (ringSheaf J O1)) ℤ :=
  Presentation.complex (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)

/-- The comparison `I'/I'² ⟶ I/I²` of polynomial conormal sheaves. -/
private def generatorConormalComparison (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ (generatorCotangent D).X (-1) :=
  ((extendComplexIdIso O1).inv.app (generatorCotangentS' D) ≫
    Presentation.Hom.map (s'toSPresentationHom D)).f (-1)

/-- The comparison `I'/I'² ⟶ I/I²` is an epimorphism. -/
private theorem generatorConormalComparison_epi (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Epi (generatorConormalComparison D) := sorry

/-- The coefficient, evaluation, and quotient maps form commuting presentation squares. -/
private theorem frontPresentationHom_laws (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq (D.f1') (FreeAlgebra.base OB1' (generatorSheaf D)) (𝟙 O1') (evalFront D) ∧
      CommSq (evalFront D) (evalToO1FromS' D) (πO1) (𝟙 O1) := sorry

private def frontPresentationHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Presentation.Hom (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)
      (𝟙 O1') πO1 where
  base := D.f1'
  middle := evalFront D
  target := 𝟙 O1
  baseSq := (frontPresentationHom_laws D).1
  targetSq := (frontPresentationHom_laws D).2

/-- Front restriction `a|_{I'} : I'/I'² ⟶ 𝒢₁`. -/
private def conormalToFrontKernel (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ conormalSource πO1 :=
  ((extendComplexIdIso O1).inv.app (generatorCotangentS' D) ≫
    Presentation.Hom.map (frontPresentationHom D)).f (-1)

/-- The coefficient, evaluation, and quotient maps form commuting presentation squares. -/
private theorem backPresentationHom_laws (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CommSq (D.t' ≫ D.f2') (FreeAlgebra.base OB1' (generatorSheaf D)) (𝟙 O2') (evalBack D) ∧
      CommSq (evalBack D) (evalToO1FromS' D) (πO2) (D.g) := sorry

private def backPresentationHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Presentation.Hom (FreeAlgebra.base OB1' (generatorSheaf D)) (evalToO1FromS' D)
      (𝟙 O2') πO2 where
  base := D.t' ≫ D.f2'
  middle := evalBack D
  target := D.g
  baseSq := (backPresentationHom_laws D).1
  targetSq := (backPresentationHom_laws D).2

/-- Back restriction `b|_{I'} : I'/I'² ⟶ g_* 𝒢₂` of the polynomial evaluation. -/
private def conormalToBackKernel (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ (restrictionAlong D.g).obj (ideal πO2) :=
  ((extendRestrictAdj D.g).homEquiv
      ((generatorCotangentS' D).X (-1)) (ideal πO2))
    ((Presentation.Hom.map (backPresentationHom D)).f (-1) ≫
      SquareZeroExtension.conormalToTarget πO2
        (inferInstance : IsFirstOrderThickening πO2).isSquareZero)

/-- The obstruction representative on `I'/I'²`, comparing back and front generator lifts. -/
private def conormalHomOverS' (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangentS' D).X (-1) ⟶ (restrictionAlong D.g).obj (ideal πO2) :=
  conormalToBackKernel D -
    conormalToFrontKernel D ≫
      SquareZeroExtension.conormalToTarget πO1
        (inferInstance : IsFirstOrderThickening πO1).isSquareZero ≫ D.ν

/-- Incoming kernel of `I'/I'² ⟶ I/I²` is annihilated by the `𝒪_{B'₁}`-obstruction representative. -/
private theorem generatorConormalComparison_kernel_comp (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    kernel.ι (generatorConormalComparison D) ≫ conormalHomOverS' D = 0 := sorry

/-- The obstruction representative `ξ : I/I² ⟶ g_* 𝒢₂` obtained by comparing front and back
generator lifts: `ξ = b|_{I'} - ν ∘ a|_{I'}`. -/
private def conormalHom (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (generatorCotangent D).X (-1) ⟶ (restrictionAlong D.g).obj (ideal πO2) :=
  @CategoryTheory.Abelian.epiDesc _ _ _ _ _ (generatorConormalComparison D)
    (generatorConormalComparison_epi D) _ (conormalHomOverS' D)
    (generatorConormalComparison_kernel_comp D)

/-- The adjunct of `conormalHom`, as an `𝒪₂`-linear map `g^* (I/I²) ⟶ 𝒢₂`. -/
private def conormalHomPull (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (extendAlong D.g).obj ((generatorCotangent D).X (-1)) ⟶ ideal πO2 :=
  ((extendRestrictAdj D.g).homEquiv
    ((generatorCotangent D).X (-1)) (ideal πO2)).symm (conormalHom D)

/-- Degreewise inverse image of the fiber-product presentation model along `g`. -/
private def pulledGeneratorCotangent (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    CochainComplex (SheafOfModules (ringSheaf J O2)) ℤ :=
  ((extendAlong D.g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (generatorCotangent D)

/-- Incoming differentials into degree `-1` of the pulled presentation vanish after composing
with the adjunct of `conormalHom`. -/
private theorem pulledGeneratorCotangent_d_comp (D : RelativeDiagram πO1 πB1 πO2 πB2)
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel k (-1)) :
    (pulledGeneratorCotangent D).d k (-1) ≫ conormalHomPull D = 0 := sorry

/-- The morphism of complexes `g^* NL(α) ⟶ 𝒢₂[-1]` associated to `conormalHom`. -/
private def conormalHomToSingle (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    pulledGeneratorCotangent D ⟶
      (CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) (-1 : ℤ)).obj
        (ideal πO2) :=
  HomologicalComplex.mkHomToSingle (conormalHomPull D) (pulledGeneratorCotangent_d_comp D)

/-- The derived class of `conormalHom` in `Ext⁽1⁾(g^* NL(α), 𝒢₂)`. -/
private def mapObstructionUnderived (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (pulledGeneratorCotangent D),
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) 0).obj
          (ideal πO2))) :=
  DerivedCategory.Q.map (conormalHomToSingle D) ≫
    ((DerivedCategory.singleFunctors
        (ringedSiteModuleCategory.{u, v, w, w} J O2)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app (ideal πO2)

/-- Derived-to-underived comparison `Lg^* NL(α) ⟶ g^* NL(α)` on the fiber-product presentation. -/
private def mapObstructionCounit (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    (SameSite.pullbackDerived D.g).obj (DerivedCategory.Q.obj (generatorCotangent D)) ⟶
      DerivedCategory.Q.obj (pulledGeneratorCotangent D) :=
  (@Functor.LeftDerived.Homotopy.cochainCounit _ _ _ _ _ _ _ _
      ((sameSiteHom D.g).modulePullback) _
      (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived (sameSiteHom D.g))).app (generatorCotangent D)

/-- The generator assignment `ℰ ⟶ 𝒪₁` is locally surjective because `π_{𝒪₁}` is a thickening. -/
private theorem generatorAssign_isLocallySurjective (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Sheaf.IsLocallySurjective (generatorAssign D) := sorry

/-- Derived identification of the fiber-product presentation with `NL(f₁)`. -/
private def generatorDerivedIso (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    DerivedCategory.Q.obj (generatorCotangent D) ≅
      DerivedCategory.Q.obj (NaiveCotangent.obj OB1 (Under.mk D.f1)) :=
  @Presentation.ofGeneratorsIso C _ J _ _ _ _ _ OB1 (Under.mk D.f1) _
    (generatorSheaf D) (generatorAssign D) (generatorAssign_isLocallySurjective D)

end MapObstructionConstruction

open MapObstructionConstruction

variable {D : RelativeDiagram πO1 πB1 πO2 πB2}

/-- The canonical class in `Ext⁽1⁾(Lg^* NL(f₁), 𝒢₂)` attached to a relative diagram. -/
def mapObstruction (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    Ext⁽(1 : ℤ)⁾(
      (SameSite.pullbackDerived D.g).obj
        (DerivedCategory.Q.obj (NaiveCotangent.obj OB1 (Under.mk D.f1))),
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) 0).obj
          (ideal πO2))) :=
  (SameSite.pullbackDerived D.g).map (generatorDerivedIso D).inv ≫
    mapObstructionCounit D ≫ mapObstructionUnderived D

/-- The adjunction identification `Hom(Ω(f₁), g_* 𝒢₂) ≃ Hom(g^* Ω(f₁), 𝒢₂)`. -/
def homOmegaPushforwardEquiv :
    (Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) ≃
      ((extendAlong D.g).obj Ω(D.f1) ⟶ ideal πO2) :=
  ((extendRestrictAdj D.g).homEquiv Ω(D.f1) (ideal πO2)).symm

namespace MapObstructionConstruction

/-- The degree-zero single functor on `𝒪₁`-modules used by `NaiveCotangent.differentialsComplex`. -/
private abbrev homOmegaSingleFunctor :
    SheafOfModules (ringSheaf J O1) ⥤
      CochainComplex (SheafOfModules (ringSheaf J O1)) ℤ :=
  HomologicalComplex.single (SheafOfModules (ringSheaf J O1)) (ComplexShape.up ℤ) 0

/-- Degree-zero single of a map `Ω(f₁) ⟶ g_* 𝒢₂`, as a map of the same single complexes used by
`NaiveCotangent.differentialsComplex`. -/
private def homOmegaSingle (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    NaiveCotangent.differentialsComplex OB1 (Under.mk D.f1) ⟶
      homOmegaSingleFunctor.obj ((restrictionAlong D.g).obj (ideal πO2)) :=
  homOmegaSingleFunctor.map α

/-- Derived-to-underived comparison `Lg^* (g_* 𝒢₂)[0] ⟶ 𝒢₂[0]`. -/
private def homOmegaCounit :
    (SameSite.pullbackDerived D.g).obj
      (DerivedCategory.Q.obj
        (homOmegaSingleFunctor.obj ((restrictionAlong D.g).obj (ideal πO2)))) ⟶
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) 0).obj (ideal πO2)) :=
  (@Functor.LeftDerived.Homotopy.cochainCounit _ _ _ _ _ _ _ _
      ((sameSiteHom D.g).modulePullback) _
      (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived (sameSiteHom D.g))).app
      (homOmegaSingleFunctor.obj ((restrictionAlong D.g).obj (ideal πO2))) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          ((sameSiteHom D.g).modulePullback) (ComplexShape.up ℤ) (0 : ℤ)).hom.app
        ((restrictionAlong D.g).obj (ideal πO2)) ≫
        (CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) 0).map
          ((pullbackExtendIso D.g).hom.app ((restrictionAlong D.g).obj (ideal πO2)) ≫
            (extendRestrictAdj D.g).counit.app (ideal πO2)))

/-- The unshifted morphism in `D(𝒪₂)` associated to a map `Ω(f₁) ⟶ g_* 𝒢₂`. -/
private def homOmegaDerived (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    (SameSite.pullbackDerived D.g).obj
        (DerivedCategory.Q.obj (NaiveCotangent.obj OB1 (Under.mk D.f1))) ⟶
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) 0).obj
          (ideal πO2)) :=
  (SameSite.pullbackDerived D.g).map
      (DerivedCategory.Q.map
        (NaiveCotangent.augmentation OB1 (Under.mk D.f1) ≫ homOmegaSingle α)) ≫
    homOmegaCounit

end MapObstructionConstruction

/-- The forward identification of the acting group with `Ext⁽0⁾(Lg^* NL(f₁), 𝒢₂)`. -/
def homOmegaExtZero (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    Ext⁽(0 : ℤ)⁾(
      (SameSite.pullbackDerived D.g).obj
        (DerivedCategory.Q.obj (NaiveCotangent.obj OB1 (Under.mk D.f1))),
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J O2) 0).obj
          (ideal πO2))) :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α)

/-- The canonical degree-zero Ext map is additive. -/
theorem homOmegaExtZero_add (α β : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    homOmegaExtZero (α + β) = homOmegaExtZero α + homOmegaExtZero β := sorry

/-- The map `Hom(Ω(f₁), g_* 𝒢₂) → Ext⁽0⁾(Lg^* NL(f₁), 𝒢₂)` is an isomorphism. -/
theorem homOmegaExtZero_bijective :
    Function.Bijective
      (fun α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2) ↦ homOmegaExtZero α) :=
  sorry

/-- The canonical degree-one obstruction vanishes precisely when the relative diagram has a filler. -/
theorem mapObstruction_eq_zero_iff (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    mapObstruction D = 0 ↔ Nonempty (FittingMap D) := sorry

/-- Any two fillers of a relative square-zero diagram differ by a unique relative-differential map. -/
theorem fittingMap_principalHomogeneous (D : RelativeDiagram πO1 πB1 πO2 πB2)
    (φ φ' : FittingMap D) :
    ∃! α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2),
      perturb α φ = φ' := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
