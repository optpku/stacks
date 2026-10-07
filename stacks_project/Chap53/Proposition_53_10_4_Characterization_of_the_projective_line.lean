module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ProjectiveLine
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Proposition 53.10.4 (Characterization of the projective line) -/
@[stacks 0C6U] #check (AlgebraicGeometry.SchemeOverField.projectiveLine_tfae :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom],
      let structureModule :=
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)
      let genusZero :=
        AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom structureModule 1 = 0
      let firstCohomologyVanishes :=
        IsZero (Scheme.Hom.cohomology X.hom structureModule 1)
      let constantGlobalFunctions :=
        Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom)
      let hasOddDegreeInvertibleModule :=
        ∃ m : ℤ, AlgebraicGeometry.Scheme.Hom.HasInvertibleModuleOfDegree X.hom
          (AlgebraicGeometry.topologicalKrullDim_eq_one X).le (2 * m + 1)
      let hasDegreeOneInvertibleModule :=
        AlgebraicGeometry.Scheme.Hom.HasInvertibleModuleOfDegree X.hom
          (AlgebraicGeometry.topologicalKrullDim_eq_one X).le 1
      let hasNormalClosedPointsOfCoprimeDegrees :=
        ∃ (n : ℕ) (x : Fin n → X.left) (a : Fin n → ℤ),
          (∀ i, x i ∈ closedPoints X.left ∧ X.left.isNormalAt (x i)) ∧
            ∑ i, a i *
              (Module.finrank k (X.left.residueField (x i)) : ℤ) = 1
      List.TFAE
        [ Nonempty (X ≅ Over.mk (ProjectiveLine.toSpec k)),
          Smooth X.hom ∧
            GeometricallyIrreducible X.hom ∧ genusZero ∧
            hasOddDegreeInvertibleModule,
          GeometricallyIntegral X.hom ∧ genusZero ∧
            Scheme.Gorenstein X.left ∧
            hasOddDegreeInvertibleModule,
          constantGlobalFunctions ∧ genusZero ∧
            Scheme.Gorenstein X.left ∧
            hasOddDegreeInvertibleModule,
          GeometricallyIntegral X.hom ∧ genusZero ∧
            hasDegreeOneInvertibleModule,
          constantGlobalFunctions ∧ genusZero ∧ hasDegreeOneInvertibleModule,
          firstCohomologyVanishes ∧ hasDegreeOneInvertibleModule,
          firstCohomologyVanishes ∧ hasNormalClosedPointsOfCoprimeDegrees ])
