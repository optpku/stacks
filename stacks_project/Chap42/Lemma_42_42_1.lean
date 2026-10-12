/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.Strata

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 42.42.1 (1): The global clopen decomposition, local-open-neighbourhood, and
component-through-a-point descriptions of the generic relative-dimension strata are equivalent. -/
@[stacks 0FE3]
#check
  (AlgebraicGeometry.Scheme.Hom.genericDimensionStrata_tfae :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ],
      List.TFAE
        [ ∃ U : ℤ → X.Opens,
            iSup U = ⊤ ∧
              Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
              (∀ n, IsClopen (U n : Set X)) ∧
              ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
                f.relativeDimensionFunction δ ξ = n
        , ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
            ∃ n : ℤ, ∀ ξ, ξ ∈ U.genericPointsInAmbient →
              f.relativeDimensionFunction δ ξ = n
        , ∀ x : X, ∃ n : ℤ, ∀ ξ : genericPoints X,
            x ∈ (genericPoints.component ξ : Set X) →
              f.relativeDimensionFunction δ ξ.1 = n
        ])

/- Lemma 42.42.1 (2): A normal scheme has a clopen decomposition by its generic
relative-dimension strata. -/
@[stacks 0FE3]
#check
  (AlgebraicGeometry.Scheme.Hom.existsGenericDimensionStrata_of_isNormal :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ],
      X.isNormal →
        ∃ U : ℤ → X.Opens,
          iSup U = ⊤ ∧
            Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
            (∀ n, IsClopen (U n : Set X)) ∧
            ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
              f.relativeDimensionFunction δ ξ = n)

/- Lemma 42.42.1 (3): A Cohen–Macaulay scheme has a clopen decomposition by its generic
relative-dimension strata. -/
@[stacks 0FE3]
#check
  (AlgebraicGeometry.Scheme.Hom.existsGenericDimensionStrata_of_cohenMacaulay :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
      [Scheme.CohenMacaulay X],
      ∃ U : ℤ → X.Opens,
        iSup U = ⊤ ∧
          Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
          (∀ n, IsClopen (U n : Set X)) ∧
          ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
            f.relativeDimensionFunction δ ξ = n)
