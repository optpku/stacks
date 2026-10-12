/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Integrality in the good setup

In Situation 82.2.1, a good algebraic space over a quasi-separated base is
integral exactly when it is reduced and irreducible, and each point is the
generic point of a unique integral closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 82.2.3 (1): in Situation 82.2.1, if `X / B` is good, then `X` is
integral if and only if `X` is reduced and `|X|` is irreducible. Decency is
automatic from the good hypotheses. Here `IsIrreducible X` is the project
reading of `|X|` irreducible from Definition 72.4.1. -/
@[stacks 0EDV]
theorem isIntegral_iff_isReduced_and_isIrreducible {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] :
    IsIntegral X ↔ IsReduced X ∧ IsIrreducible X :=
  sorry

/-- Remark 82.2.3 (2): in Situation 82.2.1, if `X / B` is good, then for any
point `ξ` of `Points X` there is a unique integral closed subspace `Z ⊂ X`
such that `ξ` is the generic point of the closed subset `|Z| ⊂ |X|`.
Uniqueness is a unique morphism over `X`. The unique `Z` is the reduced
induced integral closed subspace on the closure of `{ξ}`. -/
@[stacks 0EDV]
theorem existsUnique_integralClosedSubspace {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (ξ : Points X) :
    ∃ Z : ClosedSubspace X,
      IsIntegral Z.X ∧
        IsGenericPoint ξ Z.pointsSet ∧
          ∀ (Z' : ClosedSubspace X),
            IsIntegral Z'.X →
              IsGenericPoint ξ Z'.pointsSet →
                ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
