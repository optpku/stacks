/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Situation_69_16_1_Cohomology

/-!
# Lemma 69.16.8

A Noetherian algebraic space with vanishing `H¹` on every coherent module is an
affine scheme.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.16.8: let `S` be a scheme and let `X` be a Noetherian algebraic space over
`S`. If `H¹(X, F) = 0` for every coherent `𝒪_X`-module `F`, then `X` is an affine
scheme. -/
@[stacks 0D2V]
theorem isAffine_of_coherent_h1_zero {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent], IsZero (cohomology X F 1)) :
    IsAffine X :=
  sorry

/-- On a Noetherian algebraic space, vanishing of `H¹` on every coherent module
implies vanishing of `H¹` on every quasi-coherent module. -/
theorem hasVanishingH1_of_coherent_h1_zero {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (hH1 : ∀ (F : Modules X) [F.IsCoherent], IsZero (cohomology X F 1)) :
    HasVanishingH1 X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
