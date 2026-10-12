/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Dimension
public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Units

/-!
# Flat pullback of principal cycles by irreducible components

This file records the decomposition of the flat pullback of a principal divisor into
generic-multiplicity-weighted principal cycles on the irreducible components of the source.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- The multiplicity-weighted principal cycles on the reduced irreducible components of a
flat source form a locally finite family. -/
theorem principalComponents_locallyFinite
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (k : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (g : Y.left.functionFieldˣ) :
    LocallyFinite fun C : irreducibleComponents X.left ↦
      let η : genericPoints X.left := genericPoints.ofComponent C
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) ((k - 1) + (r : ℤ))
        ((@AlgebraicCycle.genericMultiplicity X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            η : ℤ) •
          @RationalEquivalence.principal X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) inferInstance ((k - 1) + (r : ℤ))
            η.1
            (Scheme.Hom.flatComponent_dimension δ X Y k hY f r η)
            ((Scheme.PointClosure.ι η.1 ≫ f.left).functionFieldUnitsMap
              (Scheme.Hom.flatComponent_mapsGenericPoint f.left η) g))).support := sorry

/-- The flat pullback of a principal divisor on an integral target is the locally finite sum
of the induced principal divisors on the irreducible components of the source, weighted by
their generic multiplicities. -/
theorem flatPullback_principal_eq_sum_components
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (k : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (g : Y.left.functionFieldˣ) :
    flatPullback δ X Y f r (k - 1) (Y.hom.principalDivisor δ k hY g) =
      locallyFiniteSum (X.hom.relativeDimensionFunction δ) ((k - 1) + (r : ℤ))
        (fun C : irreducibleComponents X.left ↦
          let η : genericPoints X.left := genericPoints.ofComponent C
          (@AlgebraicCycle.genericMultiplicity X.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              η : ℤ) •
            @RationalEquivalence.principal X.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction δ) inferInstance ((k - 1) + (r : ℤ))
              η.1
              (Scheme.Hom.flatComponent_dimension δ X Y k hY f r η)
              ((Scheme.PointClosure.ι η.1 ≫ f.left).functionFieldUnitsMap
                (Scheme.Hom.flatComponent_mapsGenericPoint f.left η) g))
        (principalComponents_locallyFinite δ X Y k hY f r g) := sorry

end AlgebraicGeometry.CycleGroup
