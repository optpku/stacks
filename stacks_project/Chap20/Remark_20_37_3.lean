module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Cohomology.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

noncomputable section

universe u

/- Remark 20.37.3: for K = Rlim K_n, cohomology presheaves sheafify to the actual cohomology
sheaves, the canonical inverse-limit comparisons commute, and every open has its Milnor sequence. -/
@[stacks 0BKQ] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology.comparisonDiagramAndMilnor :
    ∀ {X : RingedSpace.{u}} [IsGrothendieckAbelian X.Modules]
      {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
      (P : HomotopyLimit.Presentation Ksys K) (m : ℤ),
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
        (ShortComplex.mk leftMap ((presheafComparison P m).app (op U)) zeroComp).ShortExact))

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.sheafification_isomorphic :
  ∀ (X : RingedSpace.{u}) (K : ModuleDerived X) (m : ℤ),
    IsIsomorphic (AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.sheaf X K m)
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.presheaf X K m)))

/- In general, the inverse limit of the cohomology sheaves is not the sheafification of the
inverse limit of the cohomology presheaves. -/
#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology.sheafifyToSheafLimitComparison_not_isIso_in_general :
    ∃ (X : RingedSpace.{u}) (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ),
      ¬ IsIso (sheafifyToSheafLimitComparison Ksys m))

end
