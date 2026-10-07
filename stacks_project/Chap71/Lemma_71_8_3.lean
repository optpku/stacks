module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-!
# Complements of dense affine opens as effective Cartier divisors

On a regular Noetherian separated algebraic space, the complement of a dense
affine open subspace is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- Lemma 71.8.3: Let `S` be a scheme. Let `X` be a regular Noetherian separated
algebraic space over `S`. Let `U ⊂ X` be a dense affine open. Then there exists
an effective Cartier divisor `D ⊂ X` with `U = X \ D`. -/
@[stacks 0DML]
theorem exists_effectiveCartierDivisor_of_isSeparated
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsRegular X] [IsNoetherian X] [IsSeparated X]
    (U : OpenSubspace X) [IsAffine U.X] (hU : Dense U.pointsSet) :
    ∃ D : ClosedSubspace X,
      IsEffectiveCartierDivisor D.ι ∧ U.pointsSet = D.pointsSetᶜ :=
  sorry

/-- On a regular Noetherian separated algebraic space, the reduced induced closed
subspace on the complement of a dense affine open is an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_reducedCompl
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsRegular X] [IsNoetherian X] [IsSeparated X]
    (U : OpenSubspace X) [IsAffine U.X] (hU : Dense U.pointsSet) :
    IsEffectiveCartierDivisor (ClosedSubspaceStructure.reduced U.pointsOpens.compl).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
