/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap
public import stacks_project.Chap42.Lemma_42_36_2_Projective_space_bundle_formula_ChowMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

/-
Lemma 42.38.2: For a degree-`k` cycle `α` and a finite locally free module `E`
of rank `r`, there is a unique family `αs j ∈ CH_(k-j)(X)` whose zeroth member
is the Chow class of `α` and which satisfies the signed projective-bundle Chern
relation in `CH_(k-1)(P)`.
-/
@[stacks 02U6]
#check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.existsUniqueChernClassCap :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
      [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
      (α : CycleGroup X (p.relativeDimensionFunction δ) k),
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
              Formula.chernTerm δ p E r π hπ k i.rev (αs i.rev) = 0)

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
