/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_16_5
public import stacks_project.Chap69.Situation_69_16_1

/-!
# Proposition 69.16.7

A quasi-compact and quasi-separated algebraic space is affine if and only if
higher cohomology of quasi-coherent sheaves vanishes. More precisely, any
algebraic space as in Situation 69.16.1 is an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proposition 69.16.7: a quasi-compact and quasi-separated algebraic space
with vanishing `H^1` of every quasi-coherent module is an affine scheme.
More precisely, any algebraic space as in Situation 69.16.1 is affine. -/
@[stacks 07V6]
instance isAffine_of_hasVanishingH1 {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : IsAffine X :=
  sorry

/-- A quasi-compact and quasi-separated algebraic space is affine if and only
if it has vanishing `H^1` for every quasi-coherent module. -/
theorem isAffine_iff_hasVanishingH1 {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsAffine X ↔ HasVanishingH1 X :=
  sorry

/-- In Situation 69.16.1, the absolute canonical morphism
`toSpecA X` from `X` viewed over `Spec ℤ` to `Spec Γ(X, 𝒪_X)` is an
isomorphism. -/
instance isIso_toSpecA_of_hasVanishingH1 {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : IsIso (toSpecA X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
