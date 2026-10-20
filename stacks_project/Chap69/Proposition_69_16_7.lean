/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AffineCriterion
import StacksCheckRecall

/-!
# Proposition 69.16.7

A quasi-compact and quasi-separated algebraic space is affine if and only if
higher cohomology of quasi-coherent sheaves vanishes. More precisely, any
algebraic space as in Situation 69.16.1 is an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Proposition 69.16.7: a quasi-compact and quasi-separated algebraic space
with vanishing `H^1` of every quasi-coherent module is an affine scheme.
More precisely, any algebraic space as in Situation 69.16.1 is affine. -/
@[stacks 07V6]
#check (AlgebraicGeometry.AlgebraicSpace.isAffine_of_hasVanishingH1 :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X], IsAffine X)

/- A quasi-compact and quasi-separated algebraic space is affine if and only
if it has vanishing `H^1` for every quasi-coherent module. -/
#check (AlgebraicGeometry.AlgebraicSpace.isAffine_iff_hasVanishingH1 :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsAffine X ↔ HasVanishingH1 X)

/- In Situation 69.16.1, the absolute canonical morphism
`toSpecA X` from `X` viewed over `Spec ℤ` to `Spec Γ(X, 𝒪_X)` is an
isomorphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.isIso_toSpecA_of_hasVanishingH1 :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X], IsIso (toSpecA X))

/- A quasi-compact and quasi-separated algebraic space is affine if and only
if all positive-degree cohomology groups of quasi-coherent modules vanish. -/
#check (AlgebraicGeometry.AlgebraicSpace.isAffine_iff_cohomology_isZero :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsAffine X ↔ ∀ (F : Modules X), quasiCoherentModuleProperty X F →
      ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (cohomology X F n))
