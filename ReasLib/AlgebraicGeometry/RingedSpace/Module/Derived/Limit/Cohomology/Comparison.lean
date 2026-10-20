/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Cohomology comparisons for sequential derived limits

The stage projections induce compatible comparisons of cohomology presheaves and sheaves.
Evaluation on each open gives a Milnor sequence with the prescribed comparison as its right map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

variable {X : RingedSpace.{u}} [IsGrothendieckAbelian X.Modules]

/-- The inverse system of degree-`m` cohomology presheaves. -/
abbrev cohomologyPresheafTower (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) :
    SequentialInverseSystem ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  Ksys ⋙ cohomologyPresheafFunctor X m

/-- The inverse system of underlying additive cohomology sheaves. -/
@[stacks 0BKU "cohomology-sheaf tower of a derived inverse system"]
abbrev cohomologySheafTower (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) :
    SequentialInverseSystem (X.carrier.Sheaf AddCommGrpCat.{u}) :=
  Ksys ⋙ DerivedCategory.homologyFunctor X.Modules m ⋙ moduleUnderlyingSheaf X

variable {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}

/-- The stage-induced comparison from cohomology to the limit of cohomology presheaves. -/
def presheafComparison (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) :
    Cohomology.presheaf X K m ⟶ limit (cohomologyPresheafTower Ksys m) :=
  limit.lift _ ((cohomologyPresheafFunctor X m).mapCone P.cone)

/-- The presheaf comparison followed by a limit projection is the corresponding stage map. -/
theorem presheafComparison_π (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) (n : ℕ) :
    presheafComparison P m ≫ limit.π (cohomologyPresheafTower Ksys m) (op n) =
      (cohomologyPresheafFunctor X m).map (P.stageProjection n) := sorry

/-- The stage-induced comparison to the inverse limit of cohomology sheaves. -/
def sheafComparison (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) :
    Cohomology.sheaf X K m ⟶ limit (cohomologySheafTower Ksys m) :=
  limit.lift _
    ((DerivedCategory.homologyFunctor X.Modules m ⋙ moduleUnderlyingSheaf X).mapCone P.cone)

/-- The sheaf comparison followed by a limit projection is the underlying cohomology stage map. -/
theorem sheafComparison_π (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) (n : ℕ) :
    sheafComparison P m ≫ limit.π (cohomologySheafTower Ksys m) (op n) =
      (moduleUnderlyingSheaf X).map
        ((DerivedCategory.homologyFunctor X.Modules m).map (P.stageProjection n)) := sorry

/-- The canonical map from the sheafification of a limit to the limit of the sheafifications. -/
def sheafifyLimitComparison (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (limit (cohomologyPresheafTower Ksys m)) ⟶
      limit (cohomologyPresheafTower Ksys m ⋙
        presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
  limit.post _ _

/-- Each leg of the sheafification-limit comparison is the sheafified limit projection. -/
theorem sheafifyLimitComparison_π
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) (n : ℕ) :
    sheafifyLimitComparison Ksys m ≫
        limit.π (cohomologyPresheafTower Ksys m ⋙
          presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (op n) =
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
        (limit.π (cohomologyPresheafTower Ksys m) (op n)) := sorry

/-- The cohomology presheaf maps naturally to the underlying cohomology sheaf. -/
def presheafToCohomologySheaf (X : RingedSpace.{u}) (K : ModuleDerived X) (m : ℤ) :
    Cohomology.presheaf X K m ⟶
      (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (Cohomology.sheaf X K m) :=
  (sheafificationAdjunction _ _).unit.app _ ≫
    (sheafToPresheaf _ _).map (Cohomology.sheafificationIso X K m).hom

set_option backward.isDefEq.respectTransparency false in
/-- Limits of the stagewise presheaf-to-sheaf maps give a map to the underlying sheaf limit. -/
def limitPresheafToSheaf (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) :
    limit (cohomologyPresheafTower Ksys m) ⟶
      (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (limit (cohomologySheafTower Ksys m)) :=
  lim.map (Functor.whiskerLeft Ksys
    (Functor.whiskerLeft (cohomologyPresheafFunctor X m)
        (sheafificationAdjunction _ _).unit ≫
      Functor.whiskerRight (Cohomology.sheafificationNatIso X m).hom
        (sheafToPresheaf _ _))) ≫
    (preservesLimitIso (sheafToPresheaf _ _) (cohomologySheafTower Ksys m)).inv

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification of the presheaf limit maps canonically to the cohomology-sheaf limit. -/
def sheafifyToSheafLimitComparison
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (limit (cohomologyPresheafTower Ksys m)) ⟶
      limit (cohomologySheafTower Ksys m) :=
  sheafifyLimitComparison Ksys m ≫
    lim.map (Functor.whiskerLeft Ksys (Cohomology.sheafificationNatIso X m).hom)

/-- The stage-induced cohomology comparisons commute with the maps from presheaves to sheaves. -/
theorem comparisonSquare_commutes (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) :
    presheafComparison P m ≫ limitPresheafToSheaf Ksys m =
      presheafToCohomologySheaf X K m ≫
        (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
          (sheafComparison P m) := sorry

/-- Evaluation of the canonical presheaf comparison is the right map of the open Milnor sequence. -/
theorem presheafComparison_shortExact (P : HomotopyLimit.Presentation Ksys K)
    (m : ℤ) (U : Opens X.carrier) :
    ∃ (leftMap : SequentialInverseSystem.firstDerivedLimit
          (cohomologyPresheafTower Ksys (m - 1) ⋙
            (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) ⟶
          (Cohomology.presheaf X K m).obj (op U))
      (zeroComp : leftMap ≫ (presheafComparison P m).app (op U) = 0),
      (ShortComplex.mk leftMap ((presheafComparison P m).app (op U)) zeroComp).ShortExact := sorry

/-- Cohomology sheafification, the inverse-limit comparison square, and the open Milnor sequences
hold for every sequential derived limit. -/
theorem comparisonDiagramAndMilnor (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) :
    (presheafComparison P m ≫ limitPresheafToSheaf Ksys m =
      presheafToCohomologySheaf X K m ≫
        (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
          (sheafComparison P m)) ∧
    IsIsomorphic (Cohomology.sheaf X K m)
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (Cohomology.presheaf X K m)) ∧
    (∀ n : ℕ, IsIsomorphic (Cohomology.sheaf X (Ksys.obj (op n)) m)
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (Cohomology.presheaf X (Ksys.obj (op n)) m))) ∧
    (∀ U : Opens X.carrier, IsIsomorphic ((Cohomology.presheaf X K m).obj (op U))
      (moduleOpenHypercohomology X U K m)) ∧
    (∀ (n : ℕ) (U : Opens X.carrier),
      IsIsomorphic ((Cohomology.presheaf X (Ksys.obj (op n)) m).obj (op U))
        (moduleOpenHypercohomology X U (Ksys.obj (op n)) m)) ∧
    (∀ U : Opens X.carrier,
      ∃ (leftMap : SequentialInverseSystem.firstDerivedLimit
            (cohomologyPresheafTower Ksys (m - 1) ⋙
              (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) ⟶
            (Cohomology.presheaf X K m).obj (op U))
        (zeroComp : leftMap ≫ (presheafComparison P m).app (op U) = 0),
        (ShortComplex.mk leftMap ((presheafComparison P m).app (op U)) zeroComp).ShortExact) := sorry

/-- Sheafification of the limit of cohomology presheaves need not be the limit of cohomology sheaves. -/
theorem sheafifyToSheafLimitComparison_not_isIso_in_general :
    ∃ (X : RingedSpace.{u}) (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ),
      ¬ IsIso (sheafifyToSheafLimitComparison Ksys m) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

end
