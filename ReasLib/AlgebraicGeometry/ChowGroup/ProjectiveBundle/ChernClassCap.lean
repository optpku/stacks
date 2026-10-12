/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

/-- Reversing an index in a rank-`q + 1` projective-bundle Chern relation makes every
summand have degree `k - 1`. -/
theorem chernRelationGrade (k : ℤ) (q : ℕ) (i : Fin (q + 2)) :
    (k - (i.rev : ℕ)) + (q : ℤ) - (i : ℕ) = k - 1 := sorry

/-- A degree-`k` cycle and a represented projective bundle of a rank-`r` finite locally
free module determine a unique normalized family of Chow classes satisfying the signed
tautological Chern relation. -/
theorem existsUniqueChernClassCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    ∃! αs : (j : Fin (r + 1)) →
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)),
      αs 0 = @AlgebraicGeometry.ChowGroup.reindex X
          (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
          (sub_zero k).symm
          (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance k α) ∧
        ∑ i : Fin (r + 1),
          (-1 : ℤ) ^ (i : ℕ) •
            Formula.chernTerm δ p E r π hπ k i.rev (αs i.rev) = 0 := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
