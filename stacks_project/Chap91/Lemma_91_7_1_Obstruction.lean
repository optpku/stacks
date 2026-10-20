/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Conormal.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
public import stacks_project.Chap91.Lemma_91_7_1_Diagram

/-!
# Canonical Ext¹ obstruction of a relative first-order thickening diagram

A relative diagram determines a canonical class in
`Ext⁽1⁾(L(g)^* NL[f₁], 𝒢₂)` by comparing front and back lifts of a polynomial
presentation of `NL[f₁]` on the fiber-product generator sheaf
`𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}`. Vanishing of the class is equivalent to existence of a
fitting map, and the fiber is a torsor under `Hom(Ω[f₁], g_* 𝒢₂)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open Opposite TopologicalSpace
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback RelativeDerivation
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Module pullback along a morphism of ringed spaces is additive. -/
instance instPullbackAdditive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (Hom.pullback f).Additive := sorry

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace.Thickening

/-- The derived-category quotient of cochain complexes of `𝒪_X`-modules. -/
abbrev moduleQ (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules :=
  DerivedCategory.Q

/-- `moduleQ X` is the derived-category quotient of cochain complexes of `𝒪_X`-modules. -/
theorem moduleQ_eq (X : RingedSpace.{u}) :
    moduleQ X = DerivedCategory.Q := sorry

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

/-- Inverse-image structure maps of thickenings are locally surjective. -/
instance instInverseImage_isLocallySurjective {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsThickening h] :
    Sheaf.IsLocallySurjective (inverseImageStructureSheafHomComm h) := sorry

/-- Inverse-image structure maps of first-order thickenings are square-zero. -/
theorem inverseImage_isSquareZero {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    KernelIdeal.IsSquareZero (inverseImageStructureSheafHomComm h) := sorry

/-- The square-zero identification of the inverse-image conormal sheaf with the kernel module
over `𝒪_X`. -/
def conormalToTargetModule {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    conormalSheaf h ⟶
      (inverseImage_isSquareZero h).targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison
          (inverseImageStructureSheafHomComm h))) :=
  SheafOfModules.RingedSite.SquareZeroExtension.conormalToTarget
    (inverseImageStructureSheafHomComm h) (inverseImage_isSquareZero h)

/-- The inverse-image structure sheaf of a thickening, pulled back to the source. -/
def transportedFrontSheaf (i1 : X1 ⟶ X'1) :
    Sheaf (Opens.grothendieckTopology X1) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} i1.hom.base).obj X'1.sheaf

/-- The inverse-image structure sheaf of the back thickening, pushed forward along `g`. -/
def transportedBackSheaf (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    Sheaf (Opens.grothendieckTopology X1) CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj
    ((TopCat.Sheaf.pullback CommRingCat.{u} i2.hom.base).obj X'2.sheaf)

/-- The pushforward `g_* 𝒪_{X₂}` on `X₁`. -/
def pushforwardOX2 (g : X2 ⟶ X1) :
    Sheaf (Opens.grothendieckTopology X1) CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj X2.sheaf

/-- The comparison `i₁^{-1} 𝒪_{X'₁} ⟶ g_* 𝒪_{X₂}`. -/
def frontToPushforwardOX2 (i1 : X1 ⟶ X'1) (g : X2 ⟶ X1) :
    transportedFrontSheaf i1 ⟶ pushforwardOX2 g :=
  inverseImageStructureSheafHomComm i1 ≫ commRingSheafPushforwardMap g

/-- The comparison `g_* i₂^{-1} 𝒪_{X'₂} ⟶ g_* 𝒪_{X₂}`. -/
def backToPushforwardOX2 (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    transportedBackSheaf i2 g ⟶ pushforwardOX2 g :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
    (inverseImageStructureSheafHomComm i2)

/-- The fiber-product ring sheaf `𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}` transported to `X₁`. -/
def generatorRingSheaf (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    Sheaf (Opens.grothendieckTopology X1) CommRingCat.{u} :=
  pullback (frontToPushforwardOX2 i1 g) (backToPushforwardOX2 i2 g)

/-- The underlying sheaf of sets of the fiber-product generator ring sheaf. -/
def generatorSheaf (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    Sheaf (Opens.grothendieckTopology X1) (Type u) :=
  (sheafForget (Opens.grothendieckTopology X1)).obj (generatorRingSheaf i1 i2 g)

/-- The assignment of fiber-product generators to `𝒪_{X₁}` via the front projection. -/
def generatorAssign (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    generatorSheaf i1 i2 g ⟶
      FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f1) :=
  (sheafForget (Opens.grothendieckTopology X1)).map
    (pullback.fst (frontToPushforwardOX2 i1 g) (backToPushforwardOX2 i2 g) ≫
      inverseImageStructureSheafHomComm i1)

/-- The inverse image of `𝒪_{S'₁}` along `i₁ ≫ f'₁`. -/
def transportedS'1Sheaf (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) :
    Sheaf (Opens.grothendieckTopology X1) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (i1 ≫ f'1).hom.base).obj S'1.sheaf

/-- The structure map `i₁^{-1} f'₁^{-1} 𝒪_{S'₁} ⟶ i₁^{-1} 𝒪_{X'₁}`. -/
def transportedS'1ToFront (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) :
    transportedS'1Sheaf i1 f'1 ⟶ transportedFrontSheaf i1 :=
  (Hom.StructureSheaf.compIso i1 f'1).inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} i1.hom.base).map
      (inverseImageStructureSheafHomComm f'1)

/-- Cube identity `g ≫ i₁ ≫ f'₁ = i₂ ≫ f'₂ ≫ s'`. -/
theorem g_comp_i1_f'1_eq (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    g ≫ i1 ≫ f'1 = i2 ≫ f'2 ≫ s' := sorry

/-- The present faces of the cube give `g ≫ i₁ ≫ f'₁ = i₂ ≫ f'₂ ≫ s'`. -/
theorem gCompI1F'1 (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    g ≫ i1 ≫ f'1 = i2 ≫ f'2 ≫ s' :=
  sorry

/-- The structure map `(i₁ ≫ f'₁)^{-1} 𝒪_{S'₁} ⟶ g_* i₂^{-1} 𝒪_{X'₂}`. -/
def transportedS'1ToBack (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    transportedS'1Sheaf i1 f'1 ⟶ transportedBackSheaf i2 g :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).unit.app
      (transportedS'1Sheaf i1 f'1) ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      ((Hom.StructureSheaf.compIso g (i1 ≫ f'1)).hom ≫
        (eqToIso (congrArg
            (fun h : X2 ⟶ S'1 ↦
              (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S'1.sheaf)
            (gCompI1F'1 D))).hom ≫
          (Hom.StructureSheaf.compIso i2 (f'2 ≫ s')).inv ≫
            (TopCat.Sheaf.pullback CommRingCat.{u} i2.hom.base).map
              (inverseImageStructureSheafHomComm (f'2 ≫ s')))

/-- Front generator assignment `ℰ ⟶ i₁^{-1} 𝒪_{X'₁}`. -/
def generatorFrontAssign (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    generatorSheaf i1 i2 g ⟶
      (sheafForget (Opens.grothendieckTopology X1)).obj (transportedFrontSheaf i1) :=
  (sheafForget (Opens.grothendieckTopology X1)).map
    (pullback.fst (frontToPushforwardOX2 i1 g) (backToPushforwardOX2 i2 g))

/-- Back generator assignment `ℰ ⟶ g_* i₂^{-1} 𝒪_{X'₂}`. -/
def generatorBackAssign (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    generatorSheaf i1 i2 g ⟶
      (sheafForget (Opens.grothendieckTopology X1)).obj (transportedBackSheaf i2 g) :=
  (sheafForget (Opens.grothendieckTopology X1)).map
    (pullback.snd (frontToPushforwardOX2 i1 g) (backToPushforwardOX2 i2 g))

/-- Front evaluation `a : 𝒪_{S'₁}[ℰ] ⟶ i₁^{-1} 𝒪_{X'₁}`. -/
def evalFront (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    (transportedS'1Sheaf i1 f'1) [generatorSheaf i1 i2 g] ⟶ transportedFrontSheaf i1 :=
  (FreeAlgebra.evaluation (Under.mk (transportedS'1ToFront i1 f'1))
    (generatorSheaf i1 i2 g) (generatorFrontAssign i1 i2 g)).right

/-- Back evaluation `b : 𝒪_{S'₁}[ℰ] ⟶ g_* i₂^{-1} 𝒪_{X'₂}`. -/
def evalBack (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (transportedS'1Sheaf i1 f'1) [generatorSheaf i1 i2 g] ⟶ transportedBackSheaf i2 g :=
  (FreeAlgebra.evaluation (Under.mk (transportedS'1ToBack D))
    (generatorSheaf i1 i2 g) (generatorBackAssign i1 i2 g)).right

/-- The evaluation `𝒪_{S₁}[ℰ] ⟶ 𝒪_{X₁}` of the fiber-product presentation. -/
def evalToOX1 (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    ((TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf)
      [generatorSheaf i1 i2 g] ⟶ X1.sheaf :=
  (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f1)
    (generatorSheaf i1 i2 g) (generatorAssign D)).right

/-- The coefficient map `(i₁ ≫ f'₁)^{-1} 𝒪_{S'₁} ⟶ 𝒪_{X₁}`. -/
def transportedS'1ToOX1 (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) :
    transportedS'1Sheaf i1 f'1 ⟶ X1.sheaf :=
  transportedS'1ToFront i1 f'1 ≫ inverseImageStructureSheafHomComm i1

/-- The evaluation `𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X₁}` of the fiber-product presentation over `𝒪_{S'₁}`. -/
def evalToOX1FromS' (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (transportedS'1Sheaf i1 f'1) [generatorSheaf i1 i2 g] ⟶ X1.sheaf :=
  (FreeAlgebra.evaluation (Under.mk (transportedS'1ToOX1 i1 f'1))
    (generatorSheaf i1 i2 g) (generatorAssign D)).right

/-- The `𝒪_{S₁}`-algebra presentation of `𝒪_{X₁}` on the fiber-product generators. -/
def generatorCotangent (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    CochainComplex X1.Modules ℤ :=
  Presentation.ofGenerators (B := inverseImageStructureSheafUnder f1)
    (generatorSheaf i1 i2 g) (generatorAssign D)

/-- The inverse image of `t₁^♯`, as a map of sheaves on `X₁`. -/
def transportedT1Sharp (f1 : X1 ⟶ S1) (t1 : S1 ⟶ S'1) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (f1 ≫ t1).hom.base).obj S'1.sheaf ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf :=
  (Hom.StructureSheaf.compIso f1 t1).inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).map
      (inverseImageStructureSheafHomComm t1)

/-- Identification of `(i₁ ≫ f'₁)^{-1} 𝒪_{S'₁}` with `(f₁ ≫ t₁)^{-1} 𝒪_{S'₁}`. -/
def transportedS'1Iso (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    transportedS'1Sheaf i1 f'1 ≅
      (TopCat.Sheaf.pullback CommRingCat.{u} (f1 ≫ t1).hom.base).obj S'1.sheaf :=
  eqToIso (congrArg
    (fun h : X1 ⟶ S'1 ↦ (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S'1.sheaf)
    D.comm.front.w)

/-- The coefficient map `𝒪_{S'₁}[ℰ] ⟶ 𝒪_{S₁}[ℰ]` induced by `t₁^♯`. -/
def freeAlgebraS'toS (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (transportedS'1Sheaf i1 f'1) [generatorSheaf i1 i2 g] ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf)
        [generatorSheaf i1 i2 g] :=
  (FreeAlgebra.evaluation
      (Under.mk
        ((transportedS'1Iso D).hom ≫ transportedT1Sharp f1 t1 ≫
          FreeAlgebra.base
            ((TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf)
            (generatorSheaf i1 i2 g)))
      (generatorSheaf i1 i2 g)
      (FreeAlgebra.generator
        ((TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf)
        (generatorSheaf i1 i2 g))).right

/-- Presentation morphism from the `𝒪_{S'₁}`-polynomial presentation to the `𝒪_{S₁}`-presentation. -/
def s'toSPresentationHom (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Presentation.Hom
      (FreeAlgebra.base (transportedS'1Sheaf i1 f'1) (generatorSheaf i1 i2 g))
      (evalToOX1FromS' D)
      (FreeAlgebra.base
        ((TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf)
        (generatorSheaf i1 i2 g))
      (evalToOX1 D) where
  base := (transportedS'1Iso D).hom ≫ transportedT1Sharp f1 t1
  middle := freeAlgebraS'toS D
  target := 𝟙 _
  baseSq := sorry
  targetSq := sorry

/-- The `𝒪_{S'₁}`-algebra presentation of `𝒪_{X₁}` on the fiber-product generators. -/
def generatorCotangentS' (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    CochainComplex X1.Modules ℤ :=
  Presentation.ofGenerators (B := Under.mk (transportedS'1ToOX1 i1 f'1))
    (generatorSheaf i1 i2 g) (generatorAssign D)

/-- The comparison `I'/I'² ⟶ I/I²` of polynomial conormal sheaves. -/
def generatorConormalComparison (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (generatorCotangentS' D).X (-1) ⟶ (generatorCotangent D).X (-1) :=
  ((extendComplexIdIso X1.sheaf).inv.app (generatorCotangentS' D) ≫
    Presentation.Hom.map (s'toSPresentationHom D)).f (-1)

/-- The comparison `I'/I'² ⟶ I/I²` is an epimorphism. -/
instance generatorConormalComparison_epi
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Epi (generatorConormalComparison D) := sorry

/-- Presentation morphism from the `𝒪_{S'₁}`-polynomial presentation to the front thickening. -/
def frontPresentationHom (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Presentation.Hom
      (FreeAlgebra.base (transportedS'1Sheaf i1 f'1) (generatorSheaf i1 i2 g))
      (evalToOX1FromS' D)
      (𝟙 (transportedFrontSheaf i1))
      (inverseImageStructureSheafHomComm i1) where
  base := transportedS'1ToFront i1 f'1
  middle := evalFront i1 f'1 i2 g
  target := 𝟙 _
  baseSq := sorry
  targetSq := sorry

/-- Front restriction `a|_{I'} : I'/I'² ⟶ 𝒢₁`. -/
def conormalToFrontKernel (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (generatorCotangentS' D).X (-1) ⟶ conormalSheaf i1 :=
  ((extendComplexIdIso X1.sheaf).inv.app (generatorCotangentS' D) ≫
    Presentation.Hom.map (frontPresentationHom D)).f (-1)

/-- Presentation morphism from the `𝒪_{S'₁}`-polynomial presentation to the back thickening. -/
def backPresentationHom (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Presentation.Hom
      (FreeAlgebra.base (transportedS'1Sheaf i1 f'1) (generatorSheaf i1 i2 g))
      (evalToOX1FromS' D)
      (𝟙 (transportedBackSheaf i2 g))
      (backToPushforwardOX2 i2 g) where
  base := transportedS'1ToBack D
  middle := evalBack D
  target := commRingSheafPushforwardMap g
  baseSq := sorry
  targetSq := sorry

/-- Pushforward of `i₂^♯` along `g` is locally surjective. -/
instance instBackToPushforwardOX2_isLocallySurjective (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    Sheaf.IsLocallySurjective (backToPushforwardOX2 i2 g) := sorry

/-- Pushforward of `i₂^♯` along `g` is square-zero. -/
theorem backToPushforwardOX2_isSquareZero (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    KernelIdeal.IsSquareZero (backToPushforwardOX2 i2 g) := sorry

/-- The inclusion of the inverse-image square-zero kernel module into `𝒪_X`. -/
def targetModuleι {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    (inverseImage_isSquareZero h).targetModule
      (inferInstance : IsIso (KernelIdeal.quotientComparison
        (inverseImageStructureSheafHomComm h))) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  ⟨PresheafOfModules.homMk
    (((inverseImage_isSquareZero h).targetModuleForgetIso
          (inferInstance : IsIso (KernelIdeal.quotientComparison
            (inverseImageStructureSheafHomComm h)))).hom ≫
        (SheafOfModules.toSheaf _).map
          (KernelIdeal.ι (inverseImageStructureSheafHomComm h)) ≫
        SheafOfModules.unitUnderlyingMap
          (TopCat.Sheaf.ringSheafOfCommMap
            (inverseImageStructureSheafHomComm h))).hom
    (fun _ _ _ ↦ sorry)⟩

/-- The inclusion of the inverse-image square-zero kernel module into `𝒪_X` is a monomorphism. -/
instance instMono_targetModuleι {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    Mono (targetModuleι h) := sorry

/-- The kernel ideal of a first-order thickening maps to the pushforward of its inverse-image
square-zero kernel module. -/
def kernelIdealToPushforwardTarget {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    kernelIdealSheaf h ⟶
      (h _*).obj
        ((inverseImage_isSquareZero h).targetModule
          (inferInstance : IsIso (KernelIdeal.quotientComparison
            (inverseImageStructureSheafHomComm h)))) :=
  CategoryTheory.Abelian.monoLift ((h _*).map (targetModuleι h))
    (kernelIdealι h ≫ SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom h))
    sorry

/-- Inverse image of the kernel ideal, as a map to the inverse-image square-zero kernel module. -/
def idealModuleToTargetModule {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    idealModule h ⟶
      (inverseImage_isSquareZero h).targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison
          (inverseImageStructureSheafHomComm h))) :=
  ((pullbackPushforwardAdjunction h).homEquiv (kernelIdealSheaf h)
      ((inverseImage_isSquareZero h).targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison
          (inverseImageStructureSheafHomComm h))))).symm
    (kernelIdealToPushforwardTarget h)

/-- `idealModuleToTargetModule` is an isomorphism for a first-order thickening. -/
instance instIsIso_idealModuleToTargetModule {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    IsIso (idealModuleToTargetModule h) := sorry

/-- Identification of the inverse-image square-zero kernel module with `𝒢`. -/
def targetModuleToIdealModule {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    (inverseImage_isSquareZero h).targetModule
      (inferInstance : IsIso (KernelIdeal.quotientComparison
        (inverseImageStructureSheafHomComm h))) ⟶
      idealModule h :=
  CategoryTheory.inv (idealModuleToTargetModule h)

/-- The inclusion of the pushed-forward square-zero kernel of `i₂` into `g_* 𝒪_{X₂}`. -/
def backTargetModuleι (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1) :
    (backToPushforwardOX2_isSquareZero i2 g).targetModule
      (inferInstance : IsIso (KernelIdeal.quotientComparison (backToPushforwardOX2 i2 g))) ⟶
      SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology X1) (pushforwardOX2 g)) :=
  ⟨PresheafOfModules.homMk
    (((backToPushforwardOX2_isSquareZero i2 g).targetModuleForgetIso
          (inferInstance : IsIso (KernelIdeal.quotientComparison
            (backToPushforwardOX2 i2 g)))).hom ≫
        (SheafOfModules.toSheaf _).map (KernelIdeal.ι (backToPushforwardOX2 i2 g)) ≫
        SheafOfModules.unitUnderlyingMap
          (TopCat.Sheaf.ringSheafOfCommMap (backToPushforwardOX2 i2 g))).hom
    (fun _ _ _ ↦ sorry)⟩

/-- Restriction of scalars of `g_* 𝒪_{X₂}` as a unit module, compared with `g_* 𝒪_{X₂}`. -/
def restrictPushforwardUnitHom (g : X2 ⟶ X1) :
    (restrictionAlong (commRingSheafPushforwardMap g)).obj
      (SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology X1) (pushforwardOX2 g))) ⟶
      (g _*).obj (SheafOfModules.unit X2.ringCatSheaf) :=
  ⟨PresheafOfModules.homMk
    ((SheafOfModules.restrictScalarsCompToSheaf
        (TopCat.Sheaf.ringSheafOfCommMap (commRingSheafPushforwardMap g))).hom.app
      (SheafOfModules.unit
        (ringSheaf (Opens.grothendieckTopology X1) (pushforwardOX2 g))) ≫
      (SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit
          (TopCat.Sheaf.commRingSheafPushforwardId g.hom.base X2.sheaf))).hom
    (fun _ _ _ ↦ sorry)⟩

/-- Restriction of scalars of the back square-zero kernel module maps to `g_* 𝒢₂`. -/
def backTargetRestrictToPushforwardIdeal (i2 : X2 ⟶ X'2) (g : X2 ⟶ X1)
    [IsFirstOrderThickening i2] :
    (restrictionAlong (commRingSheafPushforwardMap g)).obj
      ((backToPushforwardOX2_isSquareZero i2 g).targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison (backToPushforwardOX2 i2 g)))) ⟶
      (g _*).obj (idealModule i2) :=
  CategoryTheory.Abelian.monoLift ((g _*).map (targetModuleι i2))
    ((restrictionAlong (commRingSheafPushforwardMap g)).map (backTargetModuleι i2 g) ≫
      restrictPushforwardUnitHom g)
    sorry ≫
    (g _*).map (targetModuleToIdealModule i2)

/-- Back restriction `b|_{I'} : I'/I'² ⟶ g_* 𝒢₂` of the polynomial evaluation. -/
def conormalToBackKernel (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (generatorCotangentS' D).X (-1) ⟶ (g _*).obj (idealModule i2) :=
  ((extendRestrictAdj (commRingSheafPushforwardMap g)).homEquiv
      ((generatorCotangentS' D).X (-1))
      ((backToPushforwardOX2_isSquareZero i2 g).targetModule
        (inferInstance : IsIso (KernelIdeal.quotientComparison
          (backToPushforwardOX2 i2 g)))))
    ((Presentation.Hom.map (backPresentationHom D)).f (-1) ≫
      SheafOfModules.RingedSite.SquareZeroExtension.conormalToTarget
        (backToPushforwardOX2 i2 g) (backToPushforwardOX2_isSquareZero i2 g)) ≫
    backTargetRestrictToPushforwardIdeal i2 g

/-- The obstruction representative on `I'/I'²`, comparing back and front generator lifts. -/
def conormalHomOverS' (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (generatorCotangentS' D).X (-1) ⟶ (g _*).obj (idealModule i2) :=
  conormalToBackKernel D -
    conormalToFrontKernel D ≫ conormalToTargetModule i1 ≫
      targetModuleToIdealModule i1 ≫ D.ν

/-- Incoming kernel of `I'/I'² ⟶ I/I²` is annihilated by the `𝒪_{S'₁}`-obstruction representative. -/
theorem generatorConormalComparison_kernel_comp
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernel.ι (generatorConormalComparison D) ≫ conormalHomOverS' D = 0 := sorry

/-- The obstruction representative `ξ : NL(α)^{-1} ⟶ g_* 𝒢₂` obtained by comparing front and
back generator lifts: `ξ = b|_{I'} - ν ∘ a|_{I'}`. -/
def conormalHom (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (generatorCotangent D).X (-1) ⟶ (g _*).obj (idealModule i2) :=
  CategoryTheory.Abelian.epiDesc (generatorConormalComparison D) (conormalHomOverS' D)
    (generatorConormalComparison_kernel_comp D)

/-- `conormalHom` compares the back and front evaluations of a lifted cotangent class. -/
theorem conormalHom_apply (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    conormalHom D =
      CategoryTheory.Abelian.epiDesc (generatorConormalComparison D) (conormalHomOverS' D)
        (generatorConormalComparison_kernel_comp D) := sorry

/-- The adjunct of `conormalHom`, as an `𝒪_{X₂}`-linear map `g^* (NL(α)^{-1}) ⟶ 𝒢₂`. -/
def conormalHomPull (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (g^*).obj ((generatorCotangent D).X (-1)) ⟶ idealModule i2 :=
  ((pullbackPushforwardAdjunction g).homEquiv
    ((generatorCotangent D).X (-1)) (idealModule i2)).symm (conormalHom D)

/-- Degreewise inverse image of the fiber-product presentation model along `g`. -/
def pulledGeneratorCotangent (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    CochainComplex X2.Modules ℤ :=
  ((g^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj (generatorCotangent D)

/-- Incoming differentials into degree `-1` of the pulled presentation vanish after composing
with the adjunct of `conormalHom`. -/
theorem pulledGeneratorCotangent_d_comp
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel k (-1)) :
    (pulledGeneratorCotangent D).d k (-1) ≫ conormalHomPull D = 0 := sorry

/-- The morphism of complexes `g^* NL(α) ⟶ 𝒢₂[-1]` associated to `conormalHom`. -/
def conormalHomToSingle (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    pulledGeneratorCotangent D ⟶
      (CochainComplex.singleFunctor X2.Modules (-1 : ℤ)).obj (idealModule i2) :=
  HomologicalComplex.mkHomToSingle (conormalHomPull D) (pulledGeneratorCotangent_d_comp D)

/-- The derived class of `conormalHom` in `Ext⁽1⁾(g^* NL(α), 𝒢₂)`. -/
def mapObstructionUnderived (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Ext⁽(1 : ℤ)⁾((moduleQ X2).obj (pulledGeneratorCotangent D),
      (moduleQ X2).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  (moduleQ X2).map (conormalHomToSingle D) ≫
    ((DerivedCategory.singleFunctors X2.Modules).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app (idealModule i2)

/-- Derived-to-underived comparison `L(g)^* NL(α) ⟶ g^* NL(α)` on the fiber-product presentation. -/
def mapObstructionCounit (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (modulePullbackDerived g).obj ((moduleQ X1).obj (generatorCotangent D)) ⟶
      (moduleQ X2).obj (pulledGeneratorCotangent D) :=
  (Functor.LeftDerived.Homotopy.cochainCounit (g^*)).app (generatorCotangent D)

/-- The generator assignment `ℰ ⟶ 𝒪_{X₁}` is locally surjective because `i₁` is a thickening. -/
instance generatorAssign_isLocallySurjective
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Sheaf.IsLocallySurjective (generatorAssign D) := sorry

/-- Modules over the inverse-image coefficient sheaf of a morphism of ringed spaces have the
standard derived-category structure. -/
instance instInverseImageUnder_hasDerivedCategory {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    HasDerivedCategory
      (SheafOfModules
        (TopCat.Sheaf.ringSheafOfComm
          (inverseImageStructureSheafUnder f).right)) :=
  HasDerivedCategory.standard _

/-- Derived identification of the fiber-product presentation with `NL[f₁]`. -/
def generatorDerivedIso (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (moduleQ X1).obj (generatorCotangent D) ≅ (moduleQ X1).obj (naiveCotangent f1) :=
  Presentation.ofGeneratorsIso (B := inverseImageStructureSheafUnder f1)
    (generatorSheaf i1 i2 g) (generatorAssign D)

/-- The canonical class in `Ext⁽1⁾(L(g)^* NL[f₁], 𝒢₂)` attached to a relative diagram. -/
def mapObstruction (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X1).obj (naiveCotangent f1)),
      (moduleQ X2).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  (modulePullbackDerived g).map (generatorDerivedIso D).inv ≫
    mapObstructionCounit D ≫ mapObstructionUnderived D

/-- `mapObstruction` is the derived class of `conormalHom`, compared with `L(g)^* NL[f₁]` and `𝒢₂`. -/
theorem mapObstruction_spec (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    mapObstruction D =
      (modulePullbackDerived g).map (generatorDerivedIso D).inv ≫
        mapObstructionCounit D ≫ mapObstructionUnderived D := sorry

/-- The adjunction identification `Hom(Ω[f₁], g_* 𝒢₂) ≃ Hom(g^* Ω[f₁], 𝒢₂)`. -/
def homOmegaPushforwardEquiv :
    (Ω[f1] ⟶ (g _*).obj (idealModule i2)) ≃ ((g^*).obj Ω[f1] ⟶ idealModule i2) :=
  ((pullbackPushforwardAdjunction g).homEquiv Ω[f1] (idealModule i2)).symm

/-- `homOmegaPushforwardEquiv` is the inverse of the pullback-pushforward hom-equivalence. -/
theorem homOmegaPushforwardEquiv_apply (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    homOmegaPushforwardEquiv α =
      ((pullbackPushforwardAdjunction g).homEquiv Ω[f1] (idealModule i2)).symm α := sorry

/-- Degree-zero single of a map `Ω[f₁] ⟶ g_* 𝒢₂`, as a map of complexes. -/
def homOmegaSingle (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    (CochainComplex.singleFunctor X1.Modules 0).obj Ω[f1] ⟶
      (CochainComplex.singleFunctor X1.Modules 0).obj ((g _*).obj (idealModule i2)) :=
  (CochainComplex.singleFunctor X1.Modules 0).map α

/-- Derived-to-underived comparison of `L(g)^* (g_* 𝒢₂)[0]` with `𝒢₂[0]`. -/
def homOmegaCounit :
    (modulePullbackDerived g).obj
      ((moduleQ X1).obj
        ((CochainComplex.singleFunctor X1.Modules 0).obj ((g _*).obj (idealModule i2)))) ⟶
    (moduleQ X2).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2)) :=
  (modulePullbackDerived g).map
      ((DerivedCategory.singleFunctorIsoCompQ X1.Modules 0).inv.app
        ((g _*).obj (idealModule i2))) ≫
    singlePullbackComparison g ((g _*).obj (idealModule i2)) 0 ≫
      (DerivedCategory.singleFunctor X2.Modules 0).map
        ((pullbackPushforwardAdjunction g).counit.app (idealModule i2)) ≫
        (DerivedCategory.singleFunctorIsoCompQ X2.Modules 0).hom.app (idealModule i2)

/-- The unshifted morphism in `D(𝒪_{X₂})` associated to a map `Ω[f₁] ⟶ g_* 𝒢₂`. -/
def homOmegaDerived (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    (modulePullbackDerived g).obj ((moduleQ X1).obj (naiveCotangent f1)) ⟶
      (moduleQ X2).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2)) :=
  (modulePullbackDerived g).map
      ((moduleQ X1).map (NaiveCotangent.augmentation f1) ≫
        (moduleQ X1).map (homOmegaSingle α)) ≫
    homOmegaCounit

/-- The forward identification of the acting group with `Ext⁽0⁾(L(g)^* NL[f₁], 𝒢₂)`. -/
def homOmegaExtZero (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    Ext⁽(0 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X1).obj (naiveCotangent f1)),
      (moduleQ X2).obj
        ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α)

/-- `homOmegaExtZero` sends a map `Ω[f₁] ⟶ g_* 𝒢₂` to the corresponding degree-zero Ext class. -/
theorem homOmegaExtZero_apply (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    homOmegaExtZero α =
      (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α) := sorry

/-- The map `Hom(Ω[f₁], g_* 𝒢₂) → Ext⁽0⁾(L(g)^* NL[f₁], 𝒢₂)` is an isomorphism. -/
theorem homOmegaExtZero_bijective :
    Function.Bijective (fun α : Ω[f1] ⟶ (g _*).obj (idealModule i2) ↦ homOmegaExtZero α) :=
  sorry

/-- The adjunction unit identifies the kernel ideal of a first-order thickening with the
pushforward of its inverse-image kernel module. -/
instance instIsIso_unit_app_kernelIdeal {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    IsIso ((pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h)) := sorry

/-- Canonical isomorphism `Ker(h^♯) ≅ h_* 𝒢`. -/
def kernelIdealPushforwardIso {X X' : RingedSpace.{u}} (h : X ⟶ X')
    [IsFirstOrderThickening h] :
    kernelIdealSheaf h ≅ (h _*).obj (idealModule h) where
  hom := (pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h)
  inv := @inv _ _ _ _ ((pullbackPushforwardAdjunction h).unit.app (kernelIdealSheaf h))
    (instIsIso_unit_app_kernelIdeal h)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The additive map of `h^♯` is an epimorphism of sheaves of abelian groups. -/
instance instEpi_toSheaf_map_unitToPushforwardObjUnit
    {X X' : RingedSpace.{u}} (h : X ⟶ X') [IsFirstOrderThickening h] :
    Epi ((SheafOfModules.toSheaf X'.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom h))) := sorry

/-- Underlying homeomorphism of a first-order thickening. -/
def thickeningBaseIso {X X' : RingedSpace.{u}} (h : X ⟶ X') [IsFirstOrderThickening h] :
    X.carrier ≅ X'.carrier :=
  @asIso TopCat.{u} _ X.carrier X'.carrier h.hom.base (instIsIso_base (i := h))

/-- Underlying additive groups of a pushforward module identify with sections on the inverse-image
open. -/
def pushforwardAppAddIso {X Y : RingedSpace.{u}} (h : X ⟶ Y) (N : X.Modules)
    (U : (Opens Y.carrier)ᵒᵖ) :
    (forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj U)) AddCommGrpCat.{u}).obj
        (((h _*).obj N).val.obj U) ≅
      (forget₂ (ModuleCat.{u}
          (X.ringCatSheaf.obj.obj (op ((Opens.map h.hom.base).obj (unop U)))))
        AddCommGrpCat.{u}).obj
        (N.val.obj (op ((Opens.map h.hom.base).obj (unop U)))) :=
  Iso.refl _

/-- Underlying additive group of the unit module identifies with the structure sheaf. -/
def unitAppAddIso {X : RingedSpace.{u}} (U : (Opens X.carrier)ᵒᵖ) :
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj U)) AddCommGrpCat.{u}).obj
        ((SheafOfModules.unit X.ringCatSheaf).val.obj U) ≅
      (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj
        ((forget₂ CommRingCat.{u} RingCat.{u}).obj (X.presheaf.obj U)) :=
  Iso.refl _

/-- The underlying additive-group element of a module section, viewed again as a module section. -/
def addToModuleSection {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (x : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) : M :=
  x

namespace FittingMap

variable {D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s'}

/-- The derivation `α ∘ d[f₁]` with values in `g_* 𝒢₂`. -/
def perturbDerivation (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    derivations f1 ((g _*).obj (idealModule i2)) :=
  (d[f1]).postcomp α.val

/-- Underlying continuous maps of `i₂ ≫ φ` and `g ≫ i₁` agree. -/
def comm_top_base_eq (φ : FittingMap D) :
    i2.hom.base ≫ φ.hom.hom.base = g.hom.base ≫ i1.hom.base :=
  congrArg (fun h : X2 ⟶ X'1 ↦ h.hom.base) φ.comm_top

/-- Open-set identification induced by `i₂ ≫ φ = g ≫ i₁`. -/
def comm_top_preimage (φ : FittingMap D) (U : Opens X'1) :
    (Opens.map g.hom.base).obj ((Opens.map i1.hom.base).obj U) =
      (Opens.map i2.hom.base).obj ((Opens.map φ.hom.hom.base).obj U) :=
  (congrArg (fun f : X2.carrier ⟶ X'1.carrier ↦ (Opens.map f).obj U)
    (comm_top_base_eq φ)).symm

/-- Identification `i₁_* g_* 𝒢₂ ≅ φ_* i₂_* 𝒢₂` along the top face of the cube. -/
def perturbTargetIso (φ : FittingMap D) :
    (i1 _*).obj ((g _*).obj (idealModule i2)) ≅
      (φ.hom _*).obj ((i2 _*).obj (idealModule i2)) :=
  (pushforwardCompIso g i1).symm.app (idealModule i2) ≪≫
    (eqToIso (congrArg (fun h : X2 ⟶ X'1 ↦ (h _*).obj (idealModule i2))
      φ.comm_top)).symm ≪≫
    (pushforwardCompIso i2 φ.hom).app (idealModule i2)

/-- The kernel-ideal section of `i₂` obtained by evaluating `α ∘ d[f₁]` on `i₁^♯` of a
section of `𝒪_{X'₁}`, then transporting along the top face. -/
def perturbKernelSection (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (kernelIdealSheaf i2).val.obj (op ((Opens.map φ.hom.hom.base).obj (unop U))) :=
  (kernelIdealPushforwardIso i2).inv.val.app
      (op ((Opens.map φ.hom.hom.base).obj (unop U)))
    ((perturbTargetIso φ).hom.val.app U
      ((perturbDerivation α).d ((commRingSheafPushforwardMap i1).hom.app U x)))

/-- Square-zero inclusion of the perturbation section into `φ_* 𝒪_{X'₂}`. -/
def perturbContribution (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (φ.hom.hom.base _* X'2.presheaf).obj U :=
  KernelIdeal.ιApp (commRingSheafPushforwardMap i2)
    (op ((Opens.map φ.hom.hom.base).obj (unop U)))
    (perturbKernelSection α φ U x)

/-- The component ring homomorphism of a perturbed structure-sheaf map. -/
def perturbRingHom (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D)
    (U : (Opens X'1.carrier)ᵒᵖ) :
    X'1.presheaf.obj U →+* (φ.hom.hom.base _* X'2.presheaf).obj U where
  toFun x := φ.hom.hom.c.app U x + perturbContribution α φ U x
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The structure-sheaf map of `φ`, modified by the square-zero inclusion of
`α ∘ d[f₁]` into `Ker(i₂^♯)`. -/
def perturbStructureSheaf (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) :
    X'1.presheaf ⟶ φ.hom.hom.base _* X'2.presheaf where
  app U := CommRingCat.ofHom (perturbRingHom α φ U)
  naturality {U V} i := sorry

/-- The filling morphism of ringed spaces obtained by perturbing `φ` by `α`. The underlying
continuous map is unchanged; the structure-sheaf map is that of `φ`, modified by the derivation
`α ∘ d[f₁]` through the square-zero kernel of `i₂`. -/
def perturbHom (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    X'2 ⟶ X'1 :=
  InducedCategory.homMk
    { base := φ.hom.hom.base
      c := perturbStructureSheaf α φ }

/-- The action of `Hom(Ω[f₁], g_* 𝒢₂)` on fitting maps, adding `α ∘ d[f₁]` through the
square-zero kernel of `i₂`. -/
def perturb (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    FittingMap D :=
  FittingMap.of (perturbHom α φ) sorry sorry sorry

/-- `perturb` does not change the underlying continuous map of the filling morphism. -/
theorem perturb_hom (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    (perturb α φ).hom.hom.base = φ.hom.hom.base := sorry

/-- Two fitting maps have the same underlying continuous map, because both fill the top face
of the cube and `i₂` is a homeomorphism. -/
def hom_base_eq (φ φ' : FittingMap D) :
    φ.hom.hom.base = φ'.hom.hom.base :=
  Iff.mp (cancel_epi i2.hom.base)
    ((comm_top_base_eq φ).trans (comm_top_base_eq φ').symm)

/-- The open of `X'₁` corresponding to an open of `X₁` along the thickening homeomorphism `i₁`. -/
def correspondingOpen (h : X1 ⟶ X'1) [IsFirstOrderThickening h] (V : Opens X1.carrier) :
    Opens X'1.carrier :=
  (Opens.map (thickeningBaseIso h).inv).obj V

/-- Identification `i₁⁻¹` of the corresponding open with the original open of `X₁`. -/
def correspondingOpenIso (h : X1 ⟶ X'1) [IsFirstOrderThickening h] (V : Opens X1.carrier) :=
  (Opens.mapMapIso (thickeningBaseIso h)).counitIso.app V

/-- `φ'^♯` as a structure-sheaf map on the same pushforward as `φ^♯`. -/
def transportedStructureSheaf (φ φ' : FittingMap D) :
    X'1.presheaf ⟶ φ.hom.hom.base _* X'2.presheaf :=
  φ'.hom.hom.c ≫ (TopCat.Presheaf.pushforwardEq (hom_base_eq φ φ').symm X'2.presheaf).hom

/-- The difference of two structure-sheaf maps, as a section of `Ker(i₂^♯)`. -/
def structureSheafDiffSection (φ φ' : FittingMap D)
    (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (kernelIdealSheaf i2).val.obj (op ((Opens.map φ.hom.hom.base).obj (unop U))) :=
  (KernelIdeal.sectionsIso (commRingSheafPushforwardMap i2)
      (op ((Opens.map φ.hom.hom.base).obj (unop U)))).inv
    ⟨(transportedStructureSheaf φ φ').app U x - φ.hom.hom.c.app U x, sorry⟩

/-- The difference of two structure-sheaf maps, as an additive sheaf morphism
`𝒪_{X'₁} ⟶ φ_* Ker(i₂^♯)`. -/
def structureSheafDiffAddHom (φ φ' : FittingMap D) :
    (SheafOfModules.toSheaf X'1.ringCatSheaf).obj (SheafOfModules.unit X'1.ringCatSheaf) ⟶
      (SheafOfModules.toSheaf X'1.ringCatSheaf).obj ((φ.hom _*).obj (kernelIdealSheaf i2)) :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x := structureSheafDiffSection φ φ' U x
          map_zero' := sorry
          map_add' := sorry }
      naturality {U V} i := sorry }

/-- Factorization of the additive structure-sheaf difference through the epimorphism `i₁^♯`. -/
def structureSheafDiffFactor (φ φ' : FittingMap D) :
    (SheafOfModules.toSheaf X'1.ringCatSheaf).obj
        ((i1 _*).obj (SheafOfModules.unit X1.ringCatSheaf)) ⟶
      (SheafOfModules.toSheaf X'1.ringCatSheaf).obj ((φ.hom _*).obj (kernelIdealSheaf i2)) :=
  CategoryTheory.Abelian.epiDesc
    ((SheafOfModules.toSheaf X'1.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom i1)))
    (structureSheafDiffAddHom φ φ') sorry

/-- Transport a section of `𝒪_{X₁}` to the corresponding open of `X'₁` along `i₁`. -/
def correspondingOpenSection (h : X1 ⟶ X'1) [IsFirstOrderThickening h]
    (V : Opens X1.carrier) (b : X1.presheaf.obj (op V)) :=
  X1.presheaf.map (correspondingOpenIso h V).hom.op b

/-- The `𝒪_{X₁}`-valued difference of two fitting maps, obtained by applying the factored
difference of structure-sheaf maps to the section of `i₁_* 𝒪_{X₁}` corresponding to `b`. -/
def differenceSection (φ φ' : FittingMap D) (V : (Opens X1.carrier)ᵒᵖ)
    (b : X1.presheaf.obj V) :
    ((g _*).obj (idealModule i2)).val.obj V :=
  ((g _*).obj (idealModule i2)).val.map (correspondingOpenIso i1 (unop V)).inv.op
    (addToModuleSection
      ((pushforwardAppAddIso i1 ((g _*).obj (idealModule i2))
          (op (correspondingOpen i1 (unop V)))).hom
        ((perturbTargetIso φ).inv.val.app (op (correspondingOpen i1 (unop V)))
          (((φ.hom _*).map (kernelIdealPushforwardIso i2).hom).val.app
            (op (correspondingOpen i1 (unop V)))
            ((structureSheafDiffFactor φ φ').hom.app (op (correspondingOpen i1 (unop V)))
              ((pushforwardAppAddIso i1 (SheafOfModules.unit X1.ringCatSheaf)
                  (op (correspondingOpen i1 (unop V)))).inv
                ((unitAppAddIso
                    (op ((Opens.map i1.hom.base).obj (correspondingOpen i1 (unop V))))).inv
                  ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
                    ((forget₂ CommRingCat.{u} RingCat.{u}).map (𝟙 _))
                    (correspondingOpenSection i1 (unop V) b)))))))))

/-- The derivation of `𝒪_{X₁}` classified by the difference of two structure-sheaf maps. -/
def differenceDerivation (φ φ' : FittingMap D) :
    derivations f1 ((g _*).obj (idealModule i2)) :=
  PresheafOfModules.Derivation'.mk
    (fun V ↦ ModuleCat.Derivation.mk (fun b ↦ differenceSection φ φ' V b)
      (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry))
    (fun _ _ _ _ ↦ sorry)

/-- The `Hom(Ω[f₁], g_* 𝒢₂)` measuring the difference of two fitting maps, obtained by
descent of the difference of structure-sheaf maps through `d[f₁]`. -/
def diff (φ φ' : FittingMap D) : Ω[f1] ⟶ (g _*).obj (idealModule i2) :=
  differentialDesc f1 (differenceDerivation φ φ')

/-- `diff` is the unique `Hom(Ω, g_* 𝒢₂)` comparing two fitting maps. -/
theorem diff_spec (φ φ' : FittingMap D) : perturb (diff φ φ') φ = φ' := sorry

end FittingMap

end AlgebraicGeometry.RingedSpace.Thickening
