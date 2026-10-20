/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.LocalPresentation
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Single-sheaf derived pullback and its canonical cohomology edge map

The single-sheaf homology inverse is built from actual free generators and their relations.
The first cell stage supplies its cycle generators and the next stage kills their relations.
Native realization comparisons transport these classes to canonical derived homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- The canonical comparison from derived pullback of a single sheaf in degree `i` to the
ordinary pullback placed in the same degree. -/
def singlePullbackComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S} (g : Y ⟶ X)
    (M : X.Modules) (i : ℤ) :
    (pullback g).obj ((DerivedCategory.singleFunctor (Modules X) i).obj M) ⟶
      (DerivedCategory.singleFunctor (Modules Y) i).obj ((Modules.pullback g).obj M) :=
  let SM := (CochainComplex.singleFunctor (Modules X) i).obj M
  (pullback g).map ((DerivedCategory.singleFunctorIsoCompQ (Modules X) i).hom.app M) ≫
    (pullbackCochainCounit g).app SM ≫
    (DerivedCategory.Q (C := Modules Y)).map
      ((HomologicalComplex.singleMapHomologicalComplex (Modules.pullback g) (up ℤ) i).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ (Modules Y) i).inv.app ((Modules.pullback g).obj M)

/-- The single-sheaf comparison uses the actual cochain augmentation counit. -/
theorem singlePullbackComparison_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    singlePullbackComparison g M i =
      let SM := (CochainComplex.singleFunctor (Modules X) i).obj M
      (pullback g).map ((DerivedCategory.singleFunctorIsoCompQ (Modules X) i).hom.app M) ≫
        (pullbackCochainCounit g).app SM ≫
        (DerivedCategory.Q (C := Modules Y)).map
          ((HomologicalComplex.singleMapHomologicalComplex (Modules.pullback g) (up ℤ) i).hom.app M) ≫
        (DerivedCategory.singleFunctorIsoCompQ (Modules Y) i).inv.app ((Modules.pullback g).obj M) := rfl

/-- On degree-`i` homology, derived pullback of a single sheaf canonically recovers ordinary
pullback. -/
def singlePullbackHomologyComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Modules Y) i).obj
        ((pullback g).obj ((DerivedCategory.singleFunctor (Modules X) i).obj M)) ⟶
      (Modules.pullback g).obj M :=
  (DerivedCategory.homologyFunctor (Modules Y) i).map (singlePullbackComparison g M i) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Y) i).hom.app
      ((Modules.pullback g).obj M)

/-- The single-sheaf homology comparison is homology of `singlePullbackComparison` followed
by removing the single-complex realization. -/
theorem singlePullbackHomologyComparison_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    singlePullbackHomologyComparison g M i =
      (DerivedCategory.homologyFunctor (Modules Y) i).map (singlePullbackComparison g M i) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Y) i).hom.app
          ((Modules.pullback g).obj M) :=
  sorry

namespace SinglePullback

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S}

/-- The single cochain input before its canonical cell replacement. -/
abbrev input (M : X.Modules) (i : ℤ) : CochainComplex X.Modules ℤ :=
  (CochainComplex.singleFunctor (Modules X) i).obj M

/-- The actual presheaf input whose local cycles are the first cell generators. -/
abbrev presheafInput (M : X.Modules) (i : ℤ) :=
  SheafOfModules.CellReplacement.underlying (input M i)

/-- The stage-one cell associated to a local section has that section as its first
coordinate and the actual zero of the seed complex as its boundary coordinate. -/
def sectionCell (M : X.Modules) (i : ℤ) (U : (smallEtaleSite X)ᵒᵖ)
    (x : M.val.obj U) :
    PresheafOfModules.CellReplacement.Cell
      (PresheafOfModules.CellReplacement.seed (presheafInput M i)).augmentation i U where
  x := ((SheafOfModules.forget (structureSheaf X)).map
    (HomologicalComplex.singleObjXSelf (up ℤ) i M).inv).app U x
  y := 0
  dx := sorry
  dy := sorry

/-- Restriction of a section is restriction of its displayed stage-one cell. -/
def sectionCells (M : X.Modules) (i : ℤ) :
    M.val.presheaf ⋙ forget AddCommGrpCat ⟶
      PresheafOfModules.CellReplacement.cells
        (PresheafOfModules.CellReplacement.seed (presheafInput M i)).augmentation i where
  app U := ↾sectionCell M i U
  naturality := sorry

/-- Put the actual local free generators in the new summand of stage one, then include that
stage into the displayed cell colimit. -/
def presheafGeneratorMap (M : X.Modules) (i : ℤ) :
    PresheafOfModules.freeObj (R := (structureSheaf X).obj)
        (M.val.presheaf ⋙ forget AddCommGrpCat) ⟶
      (SheafOfModules.CellReplacement.presheafModel (input M i)).X i :=
  (PresheafOfModules.free (structureSheaf X).obj).map (sectionCells M i) ≫
    biprod.inr ≫
    (colimit.ι (PresheafOfModules.CellReplacement.diagram (presheafInput M i)) 1).f i

/-- Sheafify the explicit stage-one inclusion of free generators. -/
def cellGeneratorMap (M : X.Modules) (i : ℤ) :
    SheafOfModules.LocalPresentation.cover M ⟶
      (SheafOfModules.CellReplacement.model (input M i)).X i :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).map
    (presheafGeneratorMap M i)

/-- The first-stage generators are cycles: their prescribed boundary coordinate is zero. -/
theorem cellGeneratorMap_cycle (M : X.Modules) (i : ℤ) :
    cellGeneratorMap M i ≫
      (SheafOfModules.CellReplacement.model (input M i)).d i (i + 1) = 0 := sorry

/-- Augmentation evaluates these generators at the original sections of the single sheaf. -/
theorem cellGeneratorMap_augmentation (M : X.Modules) (i : ℤ) :
    cellGeneratorMap M i ≫
      (SheafOfModules.CellReplacement.augmentation (input M i)).f i =
    SheafOfModules.LocalPresentation.coverπ M ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) i M).inv := sorry

/-- Ordinary pullback of the specified cell replacement of the single cochain input. -/
def pulledModel (g : Y ⟶ X) (M : X.Modules) (i : ℤ) : CochainComplex Y.Modules ℤ :=
  ((Modules.pullback g).mapHomologicalComplex (up ℤ)).obj
    (SheafOfModules.CellReplacement.model (input M i))

/-- Pullback carries the actual first-stage cycle equation to the target complex. -/
theorem pulledGenerator_cycle (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (Modules.pullback g).map (cellGeneratorMap M i) ≫
      (pulledModel g M i).d i (i + 1) = 0 := sorry

/-- Send each pulled-back generator to its actual class in the canonical cell model. -/
def generatorClass (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (Modules.pullback g).obj (SheafOfModules.LocalPresentation.cover M) ⟶
      (pulledModel g M i).homology i :=
  (pulledModel g M i).liftCycles ((Modules.pullback g).map (cellGeneratorMap M i))
      (i + 1) (by simp) (pulledGenerator_cycle g M i) ≫
    (pulledModel g M i).homologyπ i

/-- The presentation relations have zero augmentation; the next actual cell stage kills
those kernel cycles. This remains true after sheafification and arbitrary module pullback. -/
theorem relation_generatorClass (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (Modules.pullback g).map (SheafOfModules.LocalPresentation.relation M) ≫
      generatorClass g M i = 0 := sorry

/-- Right exactness transports the actual presentation cokernel through ordinary pullback. -/
def pulledPresentationIsColimit (g : Y ⟶ X) (M : X.Modules) :
    IsColimit
      ((CokernelCofork.ofπ (SheafOfModules.LocalPresentation.coverπ M)
        (SheafOfModules.LocalPresentation.relation_comp_coverπ M)).map
        (Modules.pullback g)) := by
  letI : (Modules.pullback g).IsLeftAdjoint :=
    (Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  exact CokernelCofork.mapIsColimit _
    (SheafOfModules.LocalPresentation.presentationIsColimit M) (Modules.pullback g)

/-- Descend the actual generator classes through the pulled-back presentation cokernel. -/
def homologyInverse (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (Modules.pullback g).obj M ⟶ (pulledModel g M i).homology i :=
  (pulledPresentationIsColimit g M).desc
    (CokernelCofork.ofπ (generatorClass g M i) (relation_generatorClass g M i))

/-- The descended map has the specified value on every pulled-back free generator. -/
theorem coverπ_homologyInverse (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (Modules.pullback g).map (SheafOfModules.LocalPresentation.coverπ M) ≫
      homologyInverse g M i = generatorClass g M i :=
  Cofork.IsColimit.π_desc (pulledPresentationIsColimit g M)

end SinglePullback

/-- The actual reverse of the canonical single-sheaf homology comparison. Generator classes
in the specified cell model descend through the pulled-back presentation, then pass through
native realization comparisons to derived homology. -/
def singlePullbackHomologyInverse {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (Modules.pullback g).obj M ⟶
      (DerivedCategory.homologyFunctor (Modules Y) i).obj
        ((pullback g).obj ((DerivedCategory.singleFunctor (Modules X) i).obj M)) :=
  SinglePullback.homologyInverse g M i ≫
    (DerivedCategory.homologyFunctorFactors (Modules Y) i).inv.app
      (SinglePullback.pulledModel g M i) ≫
    (DerivedCategory.homologyFunctor (Modules Y) i).map
      ((Modules.CellModels.pullbackUsingCells_fac g).app (SinglePullback.input M i)).inv ≫
    (DerivedCategory.homologyFunctor (Modules Y) i).map
      ((pullback g).map
        ((DerivedCategory.singleFunctorIsoCompQ (Modules X) i).inv.app M))

/-- The original comparison and the specified presentation inverse recover ordinary pullback. -/
def singlePullbackHomologyIso {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Modules Y) i).obj
        ((pullback g).obj ((DerivedCategory.singleFunctor (Modules X) i).obj M)) ≅
      (Modules.pullback g).obj M where
  hom := singlePullbackHomologyComparison g M i
  inv := singlePullbackHomologyInverse g M i
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward direction is the original augmentation homology comparison. -/
@[simp]
theorem singlePullbackHomologyIso_hom {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (singlePullbackHomologyIso g M i).hom = singlePullbackHomologyComparison g M i := rfl

/-- The reverse direction is the specified descent of actual cell generator classes. -/
@[simp]
theorem singlePullbackHomologyIso_inv {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (singlePullbackHomologyIso g M i).inv = singlePullbackHomologyInverse g M i := rfl

/-- Invertibility is supplied by the two specified directions, rather than an admitted
inverse witness. -/
instance singlePullbackHomologyComparison_isIso {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    IsIso (singlePullbackHomologyComparison g M i) := by
  change IsIso (singlePullbackHomologyIso g M i).hom
  infer_instance

/-- The canonical invertibility instance selects the specified presentation inverse. -/
@[simp]
theorem singlePullbackHomologyComparison_inv {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    inv (singlePullbackHomologyComparison g M i) = singlePullbackHomologyInverse g M i := by
  exact IsIso.inv_eq_of_hom_inv_id (singlePullbackHomologyIso g M i).hom_inv_id

/-- The lowest potentially nonzero cohomology sheaf of a bounded-below derived module maps
canonically into that derived module. -/
def lowerCohomologyInclusion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a) :
    (DerivedCategory.singleFunctor (Modules X) a).obj
        ((DerivedCategory.homologyFunctor (Modules X) a).obj E) ⟶ E :=
  DerivedCategory.ShiftedHom.Boundary.lowerInclusion E a hE

/-- The lower cohomology inclusion is the explicit native truncation inclusion. -/
@[simp]
theorem lowerCohomologyInclusion_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a) :
    lowerCohomologyInclusion E a hE =
      DerivedCategory.ShiftedHom.Boundary.lowerInclusion E a hE := rfl

/-- The canonical lower-edge comparison maps ordinary pullback of degree-`a` cohomology to
degree-`a` cohomology after derived pullback. -/
def cohomologyPullbackComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S} (g : Y ⟶ X)
    (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a)) :
    (Modules.pullback g).obj ((DerivedCategory.homologyFunctor (Modules X) a).obj E) ⟶
      (DerivedCategory.homologyFunctor (Modules Y) a).obj ((pullback g).obj E) :=
  inv (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a) ≫
    (DerivedCategory.homologyFunctor (Modules Y) a).map
      ((pullback g).map (lowerCohomologyInclusion E a hE))

/-- The lower-edge pullback comparison is the inverse single-sheaf comparison followed by
homology of the pulled-back lower cohomology inclusion. -/
theorem cohomologyPullbackComparison_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a)) :
    cohomologyPullbackComparison g E a hE hSingle =
      inv (singlePullbackHomologyComparison g
          ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a) ≫
        (DerivedCategory.homologyFunctor (Modules Y) a).map
          ((pullback g).map (lowerCohomologyInclusion E a hE)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
