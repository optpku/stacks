/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.FittingMap
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat

/-!
# Obstructions to compatible maps of first-order thickenings

The inverse images of the coefficient sheaves on the back space give a common-space
polynomial presentation. The difference of its two kernel maps defines a canonical derived
obstruction. Its vanishing detects compatible fillings, whose differences are classified by
relative differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
open SheafOfModules.RingedSite SheafOfModules.RingedSite.NaiveCotangent
open SheafOfModules.RingedSite.InverseImage
open Opposite TopologicalSpace
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback RelativeDerivation
open scoped CategoryTheory.Sheaf.FreeAlgebra

set_option maxRecDepth 2048

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

namespace MapObstructionConstruction

private abbrev inverse (g : X2 ⟶ X1) := TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base
private abbrev coefficient (g : X2 ⟶ X1) := (inverse g).obj X1.sheaf
private abbrev base (g : X2 ⟶ X1) (f1 : X1 ⟶ S1) :=
  (inverse g).obj ((TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).obj S1.sheaf)
private abbrev reducedMap (g : X2 ⟶ X1) (f1 : X1 ⟶ S1) : base g f1 ⟶ coefficient g :=
  (inverse g).map (inverseImageStructureSheafHomComm f1)
private abbrev targetMap (g : X2 ⟶ X1) : coefficient g ⟶ X2.sheaf :=
  inverseImageStructureSheafHomComm g
private abbrev front (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) :=
  (inverse g).obj ((TopCat.Sheaf.pullback CommRingCat.{u} i1.hom.base).obj X'1.sheaf)
private abbrev frontMap (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) : front g i1 ⟶ coefficient g :=
  (inverse g).map (inverseImageStructureSheafHomComm i1)
private abbrev back (i2 : X2 ⟶ X'2) :=
  (TopCat.Sheaf.pullback CommRingCat.{u} i2.hom.base).obj X'2.sheaf
private abbrev frontToBackQuotient (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) :=
  frontMap g i1 ≫ targetMap g
private abbrev generatorRingSheaf (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :=
  pullback (frontToBackQuotient g i1) (inverseImageStructureSheafHomComm i2)
private abbrev generatorSheaf (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :=
  (sheafForget (Opens.grothendieckTopology X2)).obj (generatorRingSheaf g i1 i2)
private abbrev generatorFront (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :
    generatorRingSheaf g i1 i2 ⟶ front g i1 := pullback.fst _ _
private abbrev generatorBack (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :
    generatorRingSheaf g i1 i2 ⟶ back i2 := pullback.snd _ _
private abbrev generatorAssign (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :=
  (sheafForget (Opens.grothendieckTopology X2)).map (generatorFront g i1 i2 ≫ frontMap g i1)

private theorem front_locallySurjective : Sheaf.IsLocallySurjective (frontMap g i1) := sorry

private theorem generatorAssign_isLocallySurjective :
    Sheaf.IsLocallySurjective (generatorAssign g i1 i2) := sorry

private abbrev thickBase (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) :=
  (inverse g).obj
    ((TopCat.Sheaf.pullback CommRingCat.{u} (i1 ≫ f'1).hom.base).obj S'1.sheaf)

private def thickBaseToFront (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) :
    thickBase g i1 f'1 ⟶ front g i1 :=
  (inverse g).map ((StructureSheaf.compIso i1 f'1).inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} i1.hom.base).map
      (inverseImageStructureSheafHomComm f'1))

private def thickBaseToBack (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    thickBase g i1 f'1 ⟶ back i2 :=
  (StructureSheaf.compIso g (i1 ≫ f'1)).hom ≫
    (eqToIso (congrArg
      (fun h : X2 ⟶ S'1 ↦ (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S'1.sheaf)
      (RelativeDiagram.g_comp_i1_f'1_eq D))).hom ≫
    (StructureSheaf.compIso i2 (f'2 ≫ s')).inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} i2.hom.base).map
      (inverseImageStructureSheafHomComm (f'2 ≫ s'))

private def thickBaseToBase (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    thickBase g i1 f'1 ⟶ base g f1 :=
  (inverse g).map ((eqToIso (congrArg
    (fun h : X1 ⟶ S'1 ↦ (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S'1.sheaf)
      D.comm.front.w)).hom ≫ (StructureSheaf.compIso f1 t1).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} f1.hom.base).map
          (inverseImageStructureSheafHomComm t1))

private abbrev generatorCotangent (g : X2 ⟶ X1) (f1 : X1 ⟶ S1)
    (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :=
  Presentation.ofGenerators (B := Under.mk (reducedMap g f1))
    (generatorSheaf g i1 i2) (generatorAssign g i1 i2)
private abbrev thickMap (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) (f'1 : X'1 ⟶ S'1) :=
  thickBaseToFront g i1 f'1 ≫ frontMap g i1
private abbrev thickCotangent (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1)
    (f'1 : X'1 ⟶ S'1) (i2 : X2 ⟶ X'2) :=
  Presentation.ofGenerators (B := Under.mk (thickMap g i1 f'1))
    (generatorSheaf g i1 i2) (generatorAssign g i1 i2)
private abbrev thickPolynomialBase (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1)
    (f'1 : X'1 ⟶ S'1) (i2 : X2 ⟶ X'2) :=
  FreeAlgebra.base (thickBase g i1 f'1) (generatorSheaf g i1 i2)
private abbrev polynomialBase (g : X2 ⟶ X1) (f1 : X1 ⟶ S1)
    (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :=
  FreeAlgebra.base (base g f1) (generatorSheaf g i1 i2)
private abbrev thickEvaluation (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1)
    (f'1 : X'1 ⟶ S'1) (i2 : X2 ⟶ X'2) :=
  (FreeAlgebra.evaluation (Under.mk (thickMap g i1 f'1))
    (generatorSheaf g i1 i2) (generatorAssign g i1 i2)).right
private abbrev evaluation (g : X2 ⟶ X1) (f1 : X1 ⟶ S1)
    (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) :=
  (FreeAlgebra.evaluation (Under.mk (reducedMap g f1))
    (generatorSheaf g i1 i2) (generatorAssign g i1 i2)).right

private def thickToBasePolynomial (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (thickBase g i1 f'1)[generatorSheaf g i1 i2] ⟶ (base g f1)[generatorSheaf g i1 i2] :=
  (FreeAlgebra.evaluation
    (Under.mk (thickBaseToBase D ≫ polynomialBase g f1 i1 i2))
    (generatorSheaf g i1 i2) (FreeAlgebra.generator (base g f1) (generatorSheaf g i1 i2))).right

private theorem thickToBasePresentationHom_laws
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    thickPolynomialBase g i1 f'1 i2 ≫ thickToBasePolynomial D =
      thickBaseToBase D ≫ polynomialBase g f1 i1 i2 ∧
    thickEvaluation g i1 f'1 i2 ≫ 𝟙 (coefficient g) =
      thickToBasePolynomial D ≫ evaluation g f1 i1 i2 := sorry

private def thickToBasePresentationHom
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Presentation.Hom (thickPolynomialBase g i1 f'1 i2) (thickEvaluation g i1 f'1 i2)
      (polynomialBase g f1 i1 i2) (evaluation g f1 i1 i2) where
  base := thickBaseToBase D
  middle := thickToBasePolynomial D
  target := 𝟙 _
  baseSq := ⟨(thickToBasePresentationHom_laws D).1.symm⟩
  targetSq := ⟨(thickToBasePresentationHom_laws D).2.symm⟩

set_option backward.isDefEq.respectTransparency false in
private def generatorConormalComparison
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    conormalSource (J := Opens.grothendieckTopology X2) (thickEvaluation g i1 f'1 i2) ⟶ conormalSource (J := Opens.grothendieckTopology X2) (evaluation g f1 i1 i2) :=
  (extendIdIso (coefficient g)).inv.app (conormalSource (J := Opens.grothendieckTopology X2) (thickEvaluation g i1 f'1 i2)) ≫
    Presentation.Hom.Conormal.map (thickToBasePresentationHom D)

set_option backward.isDefEq.respectTransparency false in
private theorem generatorConormalComparison_epi
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Epi (generatorConormalComparison D) := sorry

private def evalFront (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1)
    (f'1 : X'1 ⟶ S'1) (i2 : X2 ⟶ X'2) :
    (thickBase g i1 f'1)[generatorSheaf g i1 i2] ⟶ front g i1 :=
  (FreeAlgebra.evaluation (Under.mk (thickBaseToFront g i1 f'1)) (generatorSheaf g i1 i2)
    ((sheafForget _).map (generatorFront g i1 i2))).right
private def evalBack (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (thickBase g i1 f'1)[generatorSheaf g i1 i2] ⟶ back i2 :=
  (FreeAlgebra.evaluation (Under.mk (thickBaseToBack D)) (generatorSheaf g i1 i2)
    ((sheafForget _).map (generatorBack g i1 i2))).right

private theorem frontPresentationHom_laws
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    thickPolynomialBase g i1 f'1 i2 ≫ evalFront g i1 f'1 i2 = thickBaseToFront g i1 f'1 ≫ 𝟙 _ ∧
    thickEvaluation g i1 f'1 i2 ≫ 𝟙 (coefficient g) = evalFront g i1 f'1 i2 ≫ frontMap g i1 := sorry

private def frontPresentationHom
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Presentation.Hom (thickPolynomialBase g i1 f'1 i2) (thickEvaluation g i1 f'1 i2)
      (𝟙 (front g i1)) (frontMap g i1) where
  base := thickBaseToFront g i1 f'1
  middle := evalFront g i1 f'1 i2
  target := 𝟙 _
  baseSq := ⟨(frontPresentationHom_laws D).1.symm⟩
  targetSq := ⟨(frontPresentationHom_laws D).2.symm⟩

private theorem backPresentationHom_laws
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    thickPolynomialBase g i1 f'1 i2 ≫ evalBack D = thickBaseToBack D ≫ 𝟙 _ ∧
    thickEvaluation g i1 f'1 i2 ≫ targetMap g = evalBack D ≫
      inverseImageStructureSheafHomComm i2 := sorry

private def backPresentationHom
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Presentation.Hom (thickPolynomialBase g i1 f'1 i2) (thickEvaluation g i1 f'1 i2)
      (𝟙 (back i2)) (inverseImageStructureSheafHomComm i2) where
  base := thickBaseToBack D
  middle := evalBack D
  target := targetMap g
  baseSq := ⟨(backPresentationHom_laws D).1.symm⟩
  targetSq := ⟨(backPresentationHom_laws D).2.symm⟩

private abbrev restrictedIdeal (g : X2 ⟶ X1) (i2 : X2 ⟶ X'2) :=
  (restrictionAlong (targetMap g)).obj (idealModule i2)

private def reducedNu (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (modulePullback (J := Opens.grothendieckTopology X1)
      (K := Opens.grothendieckTopology X2) (Opens.map g.hom.base) X1.sheaf).obj (idealModule i1) ⟶ restrictedIdeal g i2 :=
  ((extendRestrictAdj (targetMap g)).homEquiv _ _)
    (((Factorization.adjunction (Opens.map g.hom.base) (commRingSheafPushforwardMap g)).homEquiv
      _ _).symm D.ν)

private def frontConormalInverse (g : X2 ⟶ X1) (i1 : X1 ⟶ X'1) :
    conormalSource (J := Opens.grothendieckTopology X2) (frontMap g i1) ⟶
      (modulePullback (J := Opens.grothendieckTopology X1)
      (K := Opens.grothendieckTopology X2) (Opens.map g.hom.base) X1.sheaf).obj (conormalSheaf i1) :=
  SheafOfModules.RingedSite.Conormal.InverseImage.comparisonInv
    (Opens.map g.hom.base)
    (ringUnit (Opens.map g.hom.base)
      ((TopCat.Sheaf.pullback CommRingCat.{u} i1.hom.base).obj X'1.sheaf))
    (ringUnit (Opens.map g.hom.base) X1.sheaf)
    (ringUnitSquare (Opens.map g.hom.base) (inverseImageStructureSheafHomComm i1))

set_option backward.isDefEq.respectTransparency false in
private def frontKernelMap (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    conormalSource (J := Opens.grothendieckTopology X2) (thickEvaluation g i1 f'1 i2) ⟶ restrictedIdeal g i2 :=
  (extendIdIso (coefficient g)).inv.app (conormalSource (J := Opens.grothendieckTopology X2) (thickEvaluation g i1 f'1 i2)) ≫
    Presentation.Hom.Conormal.map (frontPresentationHom D) ≫
    frontConormalInverse g i1 ≫
    (modulePullback (J := Opens.grothendieckTopology X1)
      (K := Opens.grothendieckTopology X2) (Opens.map g.hom.base) X1.sheaf).map
      (conormalToTargetModule i1 ≫ targetModuleToIdealModule i1) ≫ reducedNu D

set_option backward.isDefEq.respectTransparency false in
private def backKernelMap (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    conormalSource (J := Opens.grothendieckTopology X2) (thickEvaluation g i1 f'1 i2) ⟶ restrictedIdeal g i2 :=
  ((extendRestrictAdj (targetMap g)).homEquiv _ _)
    (Presentation.Hom.Conormal.map (backPresentationHom D) ≫
      conormalToTargetModule i2 ≫ targetModuleToIdealModule i2)

private def kernelRepresentative (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    conormalSource (J := Opens.grothendieckTopology X2) (thickEvaluation g i1 f'1 i2) ⟶ restrictedIdeal g i2 :=
  backKernelMap D - frontKernelMap D

private def kernelSectionInclusion (i2 : X2 ⟶ X'2) [IsFirstOrderThickening i2]
    (U : (Opens X2)ᵒᵖ)
    (x : (idealModule i2).val.obj U) : (back i2).obj.obj U :=
  KernelIdeal.ιApp (inverseImageStructureSheafHomComm i2) U
    (((inverseImage_isSquareZero i2).targetModuleForgetIso
      (inferInstance : IsIso (KernelIdeal.quotientComparison
        (inverseImageStructureSheafHomComm i2)))).hom.hom.app U
      ((idealModuleToTargetModule i2).val.app U x))

set_option backward.isDefEq.respectTransparency false in
private theorem kernelRepresentative_laws
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (U : (Opens X2)ᵒᵖ) (x : conormalIdeal (thickEvaluation g i1 f'1 i2) U) :
    kernelSectionInclusion i2 U ((kernelRepresentative D).val.app U
      ((conormalSourcePresheafUnit (thickEvaluation g i1 f'1 i2)).app U
        ((conormalIdeal (thickEvaluation g i1 f'1 i2) U).toCotangent x))) =
      ((evalBack D).hom.app U x : (back i2).obj.obj U) -
        kernelSectionInclusion i2 U ((frontKernelMap D).val.app U
          ((conormalSourcePresheafUnit (thickEvaluation g i1 f'1 i2)).app U
            ((conormalIdeal (thickEvaluation g i1 f'1 i2) U).toCotangent x))) := sorry

set_option backward.isDefEq.respectTransparency false in
private theorem generatorConormalComparison_kernel_comp
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    kernel.ι (generatorConormalComparison D) ≫ kernelRepresentative D = 0 := sorry

set_option backward.isDefEq.respectTransparency false in
private def conormalHom (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    conormalSource (J := Opens.grothendieckTopology X2) (evaluation g f1 i1 i2) ⟶ restrictedIdeal g i2 :=
  @CategoryTheory.Abelian.epiDesc _ _ _ _ _ (generatorConormalComparison D)
    (generatorConormalComparison_epi D) _ (kernelRepresentative D)
      (generatorConormalComparison_kernel_comp D)

private abbrev extendedGeneratorCotangent (g : X2 ⟶ X1) (f1 : X1 ⟶ S1)
    (i1 : X1 ⟶ X'1) (i2 : X2 ⟶ X'2) : CochainComplex X2.Modules ℤ :=
  ((extendAlong (targetMap g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (generatorCotangent g f1 i1 i2)

set_option backward.isDefEq.respectTransparency false in
private def extendedConormalHom (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    (extendedGeneratorCotangent g f1 i1 i2).X (-1) ⟶ idealModule i2 :=
  ((extendRestrictAdj (targetMap g)).homEquiv _ _).symm (conormalHom D)

private theorem extendedGeneratorCotangent_d_comp
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel k (-1)) :
    (extendedGeneratorCotangent g f1 i1 i2).d k (-1) ≫ extendedConormalHom D = 0 := sorry

private def conormalHomToSingle (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    extendedGeneratorCotangent g f1 i1 i2 ⟶
      (CochainComplex.singleFunctor X2.Modules (-1 : ℤ)).obj (idealModule i2) :=
  HomologicalComplex.mkHomToSingle (extendedConormalHom D) (extendedGeneratorCotangent_d_comp D)

private def mapObstructionUnderived (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X2.Modules)).obj (extendedGeneratorCotangent g f1 i1 i2),
      (DerivedCategory.Q (C := X2.Modules)).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  DerivedCategory.Q.map (conormalHomToSingle D) ≫
    ((DerivedCategory.singleFunctors X2.Modules).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app (idealModule i2)

set_option backward.isDefEq.respectTransparency false in
private def comparisonModel :
    extendedGeneratorCotangent g f1 i1 i2 ⟶
      ((g^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj (naiveCotangent f1) :=
  ((extendAlong (targetMap g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (Presentation.toCanonicalMap (J := Opens.grothendieckTopology X2)
      (B := Under.mk (reducedMap g f1)) (generatorSheaf g i1 i2) (generatorAssign g i1 i2) ≫
      NaiveCotangent.InverseImage.Comparison.mapInv
        (J := Opens.grothendieckTopology X1) (K := Opens.grothendieckTopology X2)
        (Opens.map g.hom.base)
        (inverseImageStructureSheafHomComm f1)) ≫
    (Factorization.complexIso (Opens.map g.hom.base) (ComplexShape.up ℤ)
      (commRingSheafPushforwardMap g)).inv.app (naiveCotangent f1)

private theorem comparisonModel_quasiIso : QuasiIso (comparisonModel (g := g) (f1 := f1)
    (i1 := i1) (i2 := i2)) := sorry

set_option backward.isDefEq.respectTransparency false in
private def derivedToPresentation :
    (modulePullbackDerived g).obj (DerivedCategory.Q.obj (naiveCotangent f1)) ⟶
      (DerivedCategory.Q (C := X2.Modules)).obj (extendedGeneratorCotangent g f1 i1 i2) :=
  (Functor.LeftDerived.Homotopy.cochainCounit (g^*)).app (naiveCotangent f1) ≫
    (Localization.isoOfHom DerivedCategory.Q
      (HomologicalComplex.quasiIso X2.Modules (ComplexShape.up ℤ)) comparisonModel
      comparisonModel_quasiIso).inv

end MapObstructionConstruction

/-- The canonical degree-one Ext obstruction to a compatible map of first-order thickenings. -/
@[no_expose] def mapObstruction (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj (DerivedCategory.Q.obj (naiveCotangent f1)),
      (DerivedCategory.Q (C := X2.Modules)).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  MapObstructionConstruction.derivedToPresentation ≫ MapObstructionConstruction.mapObstructionUnderived D

namespace MapObstructionConstruction

private theorem mapObstruction_spec (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    mapObstruction D = derivedToPresentation ≫ mapObstructionUnderived D := rfl

end MapObstructionConstruction



/-- The adjunction identification `Hom(Ω[f₁], g_* 𝒢₂) ≃ Hom(g^* Ω[f₁], 𝒢₂)`. -/
def homOmegaPushforwardEquiv :
    (Ω[f1] ⟶ (g _*).obj (idealModule i2)) ≃ ((g^*).obj Ω[f1] ⟶ idealModule i2) :=
  ((pullbackPushforwardAdjunction g).homEquiv Ω[f1] (idealModule i2)).symm

/-- `homOmegaPushforwardEquiv` is the inverse of the pullback-pushforward hom-equivalence. -/
theorem homOmegaPushforwardEquiv_apply (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    homOmegaPushforwardEquiv α =
      ((pullbackPushforwardAdjunction g).homEquiv Ω[f1] (idealModule i2)).symm α := rfl

/-- Degree-zero single of a map `Ω[f₁] ⟶ g_* 𝒢₂`, as a map of complexes. -/
def homOmegaSingle (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    (CochainComplex.singleFunctor X1.Modules 0).obj Ω[f1] ⟶
      (CochainComplex.singleFunctor X1.Modules 0).obj ((g _*).obj (idealModule i2)) :=
  (CochainComplex.singleFunctor X1.Modules 0).map α

/-- Derived-to-underived comparison of `L(g)^* (g_* 𝒢₂)[0]` with `𝒢₂[0]`. -/
def homOmegaCounit :
    (modulePullbackDerived g).obj
      ((DerivedCategory.Q (C := X1.Modules)).obj
        ((CochainComplex.singleFunctor X1.Modules 0).obj ((g _*).obj (idealModule i2)))) ⟶
    (DerivedCategory.Q (C := X2.Modules)).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2)) :=
  (modulePullbackDerived g).map
      ((DerivedCategory.singleFunctorIsoCompQ X1.Modules 0).inv.app
        ((g _*).obj (idealModule i2))) ≫
    singlePullbackComparison g ((g _*).obj (idealModule i2)) 0 ≫
      (DerivedCategory.singleFunctor X2.Modules 0).map
        ((pullbackPushforwardAdjunction g).counit.app (idealModule i2)) ≫
        (DerivedCategory.singleFunctorIsoCompQ X2.Modules 0).hom.app (idealModule i2)

/-- The unshifted morphism in `D(𝒪_{X₂})` associated to a map `Ω[f₁] ⟶ g_* 𝒢₂`. -/
def homOmegaDerived (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    (modulePullbackDerived g).obj ((DerivedCategory.Q (C := X1.Modules)).obj (naiveCotangent f1)) ⟶
      (DerivedCategory.Q (C := X2.Modules)).obj ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2)) :=
  (modulePullbackDerived g).map
      ((DerivedCategory.Q (C := X1.Modules)).map (NaiveCotangent.augmentation f1) ≫
        (DerivedCategory.Q (C := X1.Modules)).map (homOmegaSingle α)) ≫
    homOmegaCounit

/-- The forward identification of the acting group with `Ext⁽0⁾(L(g)^* NL[f₁], 𝒢₂)`. -/
def homOmegaExtZero (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    Ext⁽(0 : ℤ)⁾((modulePullbackDerived g).obj ((DerivedCategory.Q (C := X1.Modules)).obj (naiveCotangent f1)),
      (DerivedCategory.Q (C := X2.Modules)).obj
        ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α)

/-- `homOmegaExtZero` sends a map `Ω[f₁] ⟶ g_* 𝒢₂` to the corresponding degree-zero Ext class. -/
theorem homOmegaExtZero_apply (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    homOmegaExtZero α =
      (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl) (homOmegaDerived α) := rfl

/-- The map `Hom(Ω[f₁], g_* 𝒢₂) → Ext⁽0⁾(L(g)^* NL[f₁], 𝒢₂)` is an isomorphism. -/
theorem homOmegaExtZero_bijective :
    Function.Bijective (fun α : Ω[f1] ⟶ (g _*).obj (idealModule i2) ↦ homOmegaExtZero α) :=
  sorry

/-- Maps from relative differentials to the pushforward kernel form the additive group of
degree-zero extensions from the derived pullback of the naive cotangent complex. -/
def homOmegaExtZeroAddEquiv :
    (Ω[f1] ⟶ (g _*).obj (idealModule i2)) ≃+
      Ext⁽(0 : ℤ)⁾((modulePullbackDerived g).obj
        ((DerivedCategory.Q (C := X1.Modules)).obj (naiveCotangent f1)),
        (DerivedCategory.Q (C := X2.Modules)).obj
          ((CochainComplex.singleFunctor X2.Modules 0).obj (idealModule i2))) :=
  let single := CochainComplex.singleFunctor X1.Modules 0
  let quotient := DerivedCategory.Q (C := X1.Modules)
  let pullback := modulePullbackDerived g
  let additivity : pullback.Additive :=
    @Functor.IsTriangulated.instAdditive _ _ _ _ _ _ pullback
      (modulePullbackDerived.commShift g) _ _ _ _ _ _ _ _
      (modulePullbackDerived.isTriangulated g)
  let augmentation := quotient.map (NaiveCotangent.augmentation f1)
  let counit := homOmegaCounit (g := g) (i2 := i2)
  let derivedHom := (Preadditive.rightComp _ counit).comp
    ((@Functor.mapAddHom _ _ _ _ _ _ pullback additivity _ _).comp
      ((Preadditive.leftComp _ augmentation).comp
        (quotient.mapAddHom.comp single.mapAddHom)))
  let zeroHom := (CategoryTheory.ShiftedHom.zeroLinearEquiv ℤ _ _).symm.toAddEquiv.toAddMonoidHom
  AddEquiv.ofBijective (zeroHom.comp derivedHom) homOmegaExtZero_bijective

/-- The canonical obstruction vanishes exactly when a compatible filling exists. -/
theorem mapObstruction_eq_zero_iff
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    mapObstruction D = 0 ↔ Nonempty (FittingMap D) := sorry

/-- Compatible fillings form a principal homogeneous space under the differential Hom group. -/
theorem fittingMap_principalHomogeneous
    (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s')
    (φ φ' : FittingMap D) :
    ∃! α : Ω[f1] ⟶ (g _*).obj (idealModule i2), FittingMap.perturb α φ = φ' := sorry

end AlgebraicGeometry.RingedSpace.Thickening
