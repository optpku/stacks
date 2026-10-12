/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap69.Situation_69_16_1_Cohomology
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
import StacksCheckRecall

@[expose] public section

/- Situation 69.16.1 (1): Here S is a scheme and X is a quasi-compact and quasi-separated
algebraic space over S with the following property: for every quasi-coherent 𝒪_X-module F
we have H^1(X, F) = 0. -/
@[stacks 07UY] #check AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact
@[stacks 07UY] #check AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated
@[stacks 07UY] #check AlgebraicGeometry.AlgebraicSpace.HasVanishingH1

/- Situation 69.16.1 (2): We set A = Γ(X, 𝒪_X). -/
@[stacks 07UY] #check AlgebraicGeometry.AlgebraicSpace.globalSectionsRing
