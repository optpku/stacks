/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Principal

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/- Lemma 42.20.1: For a flat morphism of relative dimension `r` to an integral scheme,
flat pullback of a principal divisor is the multiplicity-weighted sum of the induced
principal divisors on the irreducible components of the source. -/
@[stacks 0EPH] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_principal_eq_sum_components :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [IsIntegral Y.left] (k : ℤ)
      (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k)
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (g : Y.left.functionFieldˣ),
      AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r (k - 1)
          (Y.hom.principalDivisor δ k hY g) =
        AlgebraicGeometry.CycleGroup.locallyFiniteSum
          (X.hom.relativeDimensionFunction δ) ((k - 1) + (r : ℤ))
          (fun C : irreducibleComponents X.left ↦
            let η : genericPoints X.left := genericPoints.ofComponent C
            (@AlgebraicGeometry.AlgebraicCycle.genericMultiplicity X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                η : ℤ) •
              @AlgebraicGeometry.RationalEquivalence.principal X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction δ) inferInstance ((k - 1) + (r : ℤ))
                η.1
                (AlgebraicGeometry.Scheme.Hom.flatComponent_dimension
                  δ X Y k hY f r η)
                ((Scheme.PointClosure.ι η.1 ≫ f.left).functionFieldUnitsMap
                  (AlgebraicGeometry.Scheme.Hom.flatComponent_mapsGenericPoint f.left η) g))
          (AlgebraicGeometry.CycleGroup.principalComponents_locallyFinite
            δ X Y k hY f r g))
