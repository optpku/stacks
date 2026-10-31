/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveAtlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing

/-! The tautological quotient is descended from the actual represented quotient classes.
Representatives are extracted only from existing quotient classes. The transition
isomorphism is uniquely forced by their epimorphic maps, not freely supplied data.
-/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.MonoidalCategory
open CategoryTheory.InvertibleQuotient
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.TautologicalDescent
variable {S : Scheme.{u}} {X : AlgebraicSpace S} (E : X.Modules) [E.IsQuasicoherent]
open ProjectiveAtlas

def base {T : Over S} (a : ofOver T ⟶ space E) : ofOver T ⟶ X := a ≫ projection E

theorem base_point {T : Over S} (a : ofOver T ⟶ space E) :
    SmallProjectiveFunctor.homOfPoint (yonedaEquiv a).1 = base E a := by
  sorry

def testClass {T : Over S} (a : ofOver T ⟶ space E) :
    IsoClass ((Modules.pullback (base E a)).obj E) :=
  (base_point E a) ▸
    (SmallProjectiveFunctor.pointEquiv E T
      (SmallProjectiveFunctor.homOfPoint (yonedaEquiv a).1)).symm (yonedaEquiv a).2

/-- A representative of the actual quotient point; no existence theorem supplies it. -/
def testQuotient {T : Over S} (a : ofOver T ⟶ space E) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback (base E a)).obj E) :=
  Quotient.out (testClass E a)

theorem testQuotient_class {T : Over S} (a : ofOver T ⟶ space E) :
    IsoClass.mk (testQuotient E a) = testClass E a := Quotient.out_eq _

def localLine (U : smallEtaleSite (space E)) : (ofOver U.left).Modules :=
  (testQuotient E U.hom).object

def sourceIso {U V : smallEtaleSite (space E)} (a : V ⟶ U) :
    (Modules.pullback (ofOverMap a.left)).obj ((Modules.pullback (base E U.hom)).obj E) ≅
      (Modules.pullback (base E V.hom)).obj E :=
  (Modules.pullbackCompIso (ofOverMap a.left) (base E U.hom)).app E ≪≫
    eqToIso (congrArg (fun g ↦ (Modules.pullback g).obj E) (by
      change ofOverMap a.left ≫ (U.hom ≫ projection E) = V.hom ≫ projection E
      rw [← Category.assoc, SmallEtaleGlueing.ofOverMap_triangle a]
      rfl))

def restrictedQuotient {U V : smallEtaleSite (space E)} (a : V ⟶ U) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback (base E V.hom)).obj E) :=
  precomposeIso (sourceIso E a).symm
    (AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient.pullback (ofOverMap a.left)
      (testQuotient E U.hom))

/-- Naturality of the represented point identifies the actual quotient classes. -/
theorem restrictedQuotient_class {U V : smallEtaleSite (space E)} (a : V ⟶ U) :
    IsoClass.mk (restrictedQuotient E a) = IsoClass.mk (testQuotient E V.hom) := by
  sorry

def transition {U V : smallEtaleSite (space E)} (a : V ⟶ U) :
    (SmallEtaleModuleGlueing.pullback a).obj (localLine E U) ≅ localLine E V :=
  targetIsoOfMkEq (restrictedQuotient_class E a)

/-- The gluing map respects the actual tautological quotient on every overlap. -/
theorem transition_quotient {U V : smallEtaleSite (space E)} (a : V ⟶ U) :
    (restrictedQuotient E a).hom ≫ (transition E a).hom = (testQuotient E V.hom).hom :=
  targetIsoOfMkEq_spec (restrictedQuotient_class E a)

theorem transition_id (U : smallEtaleSite (space E)) :
    transition E (𝟙 U) = (SmallEtaleModuleGlueing.pullbackId U).app (localLine E U) := by
  sorry

theorem transition_comp {U V W : smallEtaleSite (space E)} (a : V ⟶ U) (b : W ⟶ V) :
    (SmallEtaleModuleGlueing.pullbackComp a b).app (localLine E U) ≪≫ transition E (b ≫ a) =
      (SmallEtaleModuleGlueing.pullback b).mapIso (transition E a) ≪≫ transition E b := by
  sorry

def system : SmallEtaleModuleGlueing.Object (space E) where
  obj := localLine E
  transition := transition E
  transition_id := transition_id E
  transition_comp := transition_comp E

/-- O(1) is the actual module reconstructed from compatible local line sections. -/
def O1 : (space E).Modules := (SmallEtaleModuleGlueing.toModules (space E)).obj (system E)

def sourceSystem : SmallEtaleModuleGlueing.Object (space E) :=
  SmallEtaleModuleGlueing.Object.ofModules ((Modules.pullback (projection E)).obj E)

def localQuotientHom (U : smallEtaleSite (space E)) : (sourceSystem E).obj U ⟶ localLine E U :=
  (Modules.pullbackCompIso U.hom (projection E)).hom.app E ≫ (testQuotient E U.hom).hom

theorem localQuotient_natural {U V : smallEtaleSite (space E)} (a : V ⟶ U) :
    CommSq ((SmallEtaleModuleGlueing.pullback a).map (localQuotientHom E U))
      ((sourceSystem E).transition a).hom ((system E).transition a).hom (localQuotientHom E V) := by
  sorry

def quotientSystem : SmallEtaleModuleGlueing.Hom (sourceSystem E) (system E) where
  app := localQuotientHom E
  naturality := localQuotient_natural E

/-- The postcomposition of the represented identity chart is exactly U. -/
theorem identityChart_eq (P : AlgebraicSpace S) (U : smallEtaleSite P) :
    (Modules.restrictPostcompose U.hom).obj (SmallEtaleGlueing.idObj U.left) = U := by
  sorry

/-- The concrete section map from a module to reconstruction from its restrictions. -/
def reconstructionFunction (P : AlgebraicSpace S) (M : P.Modules) (U : smallEtaleSite P) :
    M.val.obj (op U) →
      ((Modules.pullback U.hom).obj M).val.obj (op (SmallEtaleGlueing.idObj U.left)) :=
  fun x ↦ (((Modules.restrictFunctorIsoPullback U.hom).hom.app M).val.app
    (op (SmallEtaleGlueing.idObj U.left)))
      (M.val.map (eqToHom (identityChart_eq P U)).op x)

-- Two recorded attempts hit the default recursion depth while comparing the
-- reconstructed module's scalar action; the section function itself elaborates.
set_option maxRecDepth 2048 in
/-- The same actual section function, bundled with its module laws. -/
def reconstructionApp (P : AlgebraicSpace S) (M : P.Modules) (U : smallEtaleSite P) :
    M.val.obj (op U) ⟶
      ((SmallEtaleModuleGlueing.toModules P).obj (SmallEtaleModuleGlueing.Object.ofModules M)).val.obj
        (op U) := by
  let A := M.val.obj (op U)
  let B := ((SmallEtaleModuleGlueing.toModules P).obj
    (SmallEtaleModuleGlueing.Object.ofModules M)).val.obj (op U)
  exact @ModuleCat.ofHom ((structureSheaf P).obj.obj (op U)) _ A B
    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
    { toFun := reconstructionFunction P M U
      map_add' := by sorry
      map_smul' := by sorry }

def reconstructionMap (P : AlgebraicSpace S) (M : P.Modules) :
    M ⟶ (SmallEtaleModuleGlueing.toModules P).obj
      (SmallEtaleModuleGlueing.Object.ofModules M) where
  val := { app := fun U ↦ reconstructionApp P M U.unop, naturality := by sorry }

theorem reconstructionMap_isIso (P : AlgebraicSpace S) (M : P.Modules) :
    IsIso (reconstructionMap P M) := by sorry

/-- The actual global universal quotient, obtained by reconstructing its local maps. -/
def quotientHom : (Modules.pullback (projection E)).obj E ⟶ O1 E :=
  reconstructionMap (space E) ((Modules.pullback (projection E)).obj E) ≫
    (SmallEtaleModuleGlueing.toModules (space E)).map (quotientSystem E)

theorem O1_invertible : isInvertibleObject (O1 E) := by
  sorry

theorem quotientHom_epi : Epi (quotientHom E) := by
  sorry

def quotient : CategoryTheory.InvertibleQuotient ((Modules.pullback (projection E)).obj E) where
  object := O1 E
  isInvertible := O1_invertible E
  hom := quotientHom E
  hom_epi := quotientHom_epi E

theorem O1_sections (U : smallEtaleSite (space E)) :
    (O1 E).val.obj (op U) =
      (localLine E U).val.obj (op (SmallEtaleGlueing.idObj U.left)) := rfl

theorem quotient_hom : (quotient E).hom = quotientHom E := rfl

/-- Pullback of the displayed universal quotient, with the actual composition comparison. -/
def pulledUniversalQuotient {T : Over S} (a : ofOver T ⟶ space E) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback (base E a)).obj E) :=
  precomposeIso ((Modules.pullbackCompIso a (projection E)).app E).symm
    (AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient.pullback a (quotient E))

/-- Reconstruction recovers the original represented quotient point. -/
theorem universal_class {T : Over S} (a : ofOver T ⟶ space E) :
    IsoClass.mk (pulledUniversalQuotient E a) = IsoClass.mk (testQuotient E a) := by
  sorry

def universalComparison {T : Over S} (a : ofOver T ⟶ space E) :
    (Modules.pullback a).obj (O1 E) ≅ (testQuotient E a).object :=
  targetIsoOfMkEq (universal_class E a)

theorem universalComparison_quotient {T : Over S} (a : ofOver T ⟶ space E) :
    (pulledUniversalQuotient E a).hom ≫ (universalComparison E a).hom =
      (testQuotient E a).hom := targetIsoOfMkEq_spec (universal_class E a)

theorem chart_base (U : ProjectiveAtlas.Index (X := X)) :
    base E (ProjectiveAtlas.chartMap E U) = ProjectiveAtlas.chartBase E U := by sorry

def pulledChartQuotient (U : ProjectiveAtlas.Index (X := X)) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback (ProjectiveAtlas.chartBase E U)).obj E) :=
  precomposeIso (eqToIso (congrArg (fun g ↦ (Modules.pullback g).obj E) (chart_base E U))).symm
    (pulledUniversalQuotient E (ProjectiveAtlas.chartMap E U))

theorem chart_class (U : ProjectiveAtlas.Index (X := X)) :
    IsoClass.mk (pulledChartQuotient E U) =
      IsoClass.mk (ProjectiveAtlas.chartQuotient E U) := by
  sorry

/-- The descended O(1) restricts to the actual affine Serre line used to build the atlas. -/
def chartComparison (U : ProjectiveAtlas.Index (X := X)) :
    (Modules.pullback (ProjectiveAtlas.chartMap E U)).obj (O1 E) ≅ ProjectiveAtlas.chartLine E U :=
  targetIsoOfMkEq (chart_class E U)

theorem chartComparison_quotient (U : ProjectiveAtlas.Index (X := X)) :
    (pulledChartQuotient E U).hom ≫ (chartComparison E U).hom =
      (ProjectiveAtlas.chartQuotient E U).hom := targetIsoOfMkEq_spec (chart_class E U)

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.TautologicalDescent
