module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap110.Lemma_110_75_1_McQuillan

/-!
# A non-McQuillan affine formal algebraic space
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- Lemma 110.75.1: there exists an affine formal algebraic space which is not
McQuillan. -/
@[stacks 0CBC]
theorem exists_isAffineFormalAlgebraicSpace_not_isMcQuillan :
    ∃ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v))))
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v))),
      IsAffineFormalAlgebraicSpace X ∧ ¬ IsMcQuillan X := sorry

end AlgebraicGeometry
