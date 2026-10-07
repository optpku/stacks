module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.FormulaMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Rational equivalence and Chern-class cap products

This file records that a family satisfying the projective-bundle characterization of
Chern-class cap products descends through rational equivalence.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

/-- A family of cycle-level Chern-cap maps has the projective-bundle
characterization when its zeroth component is the Chow class and its components
satisfy the signed projective-bundle Chern relation. -/
def IsChernClassCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (c : (j : Fin (r + 1)) →
      CycleGroup X (p.relativeDimensionFunction δ) k →+
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))) : Prop :=
  ∀ α,
    c 0 α = @reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) ∧
      match r, hE with
      | 0, hE =>
          @Formula.formulaMap S X P inferInstance δ inferInstance p inferInstance
            E 0 hE π hπ k (fun i ↦ Fin.elim0 i) = 0
      | q + 1, hE =>
          ∑ i : Fin (q + 2),
            (-1 : ℤ) ^ (i : ℕ) •
              @reindex P
                (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
                  (Formula.locallyOfFiniteTypeComp hπ p (q + 1)) inferInstance)
                ((π ≫ p).relativeDimensionFunction δ)
                (@instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
                  inferInstance (Formula.locallyOfFiniteTypeComp hπ p (q + 1)) δ inferInstance)
                ((k - (i.rev : ℕ)) + (q : ℤ) - (i : ℕ)) (k - 1)
                (chernRelationGrade k q i)
                (@Formula.pullbackThenC1PowerCap S X P inferInstance δ inferInstance
                  p inferInstance E q hE π hπ
                  (k - (i.rev : ℕ)) (i : ℕ) (c i.rev α)) = 0

/-- A family is a Chern-cap family exactly when each cycle satisfies the zeroth
component condition and the signed projective-bundle Chern relation. -/
theorem isChernClassCap_iff
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (c : (j : Fin (r + 1)) →
      CycleGroup X (p.relativeDimensionFunction δ) k →+
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))) :
    IsChernClassCap δ p E r π hπ k c ↔
      ∀ α,
        c 0 α = @reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
            (sub_zero k).symm
            (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
              (p.relativeDimensionFunction δ) inferInstance k α) ∧
          match r, hE with
          | 0, hE =>
              @Formula.formulaMap S X P inferInstance δ inferInstance p inferInstance
                E 0 hE π hπ k (fun i ↦ Fin.elim0 i) = 0
          | q + 1, hE =>
              ∑ i : Fin (q + 2),
                (-1 : ℤ) ^ (i : ℕ) •
                  @reindex P
                    (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
                      (Formula.locallyOfFiniteTypeComp hπ p (q + 1)) inferInstance)
                    ((π ≫ p).relativeDimensionFunction δ)
                    (@instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
                      inferInstance (Formula.locallyOfFiniteTypeComp hπ p (q + 1)) δ inferInstance)
                    ((k - (i.rev : ℕ)) + (q : ℤ) - (i : ℕ)) (k - 1)
                    (chernRelationGrade k q i)
                    (@Formula.pullbackThenC1PowerCap S X P inferInstance δ inferInstance
                      p inferInstance E q hE π hπ
                      (k - (i.rev : ℕ)) (i : ℕ) (c i.rev α)) = 0 := sorry

/-- A Chern-cap family kills rational-equivalence boundaries in every component. -/
theorem IsChernClassCap.boundaries_le_ker
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (c : (j : Fin (r + 1)) →
      CycleGroup X (p.relativeDimensionFunction δ) k →+
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)))
    (hc : IsChernClassCap δ p E r π hπ k c) (j : Fin (r + 1)) :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k ≤ (c j).ker := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle

namespace AlgebraicGeometry.ChowGroup

/-- Intersection with a component of a Chern-class cap family sends rationally equivalent
cycles to the same Chow class. -/
theorem chernClassCap_eq_of_rationallyEquivalent
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (c : (j : Fin (r + 1)) →
      CycleGroup X (p.relativeDimensionFunction δ) k →+
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)))
    (hc : ProjectiveBundle.IsChernClassCap δ p E r π hπ k c)
    (α β : CycleGroup X (p.relativeDimensionFunction δ) k)
    (h_rational : @RationalEquivalence.RationallyEquivalent X
      (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k α β)
    (j : Fin (r + 1)) :
    c j α = c j β := sorry

end AlgebraicGeometry.ChowGroup
