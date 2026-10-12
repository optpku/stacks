/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap71.Lemma_71_12_1_Compatibility
public import stacks_project.Chap71.Lemma_71_12_1_Restrict

/-!
# Lemma 71.12.1

A map of quasi-coherent graded `𝒪_X`-algebras on an algebraic space induces a
canonical relative projective-spectrum map, uniquely characterized by étale
localization to Constructions Lemma 27.18.1.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open CategoryTheory
open SheafOfModules.RingedSite

universe u

/- Lemma 71.12.1: Let S be a scheme, X an algebraic space over S, and ψ a map of
quasi-coherent graded 𝒪_X-algebras. Set P = underline{Proj}_X(𝒜) ⟶ X and
Q = underline{Proj}_X(ℬ) ⟶ X. There is a unique relative projective-spectrum map
(U(ψ), r_ψ, θ_ψ) over X whose restriction to every scheme W étale over X equals
the triple associated to ψ|_W of Constructions Lemma 27.18.1.
-/
@[stacks 085F] #check RelativeProjMap.existsUnique_of_etale

#check RelativeProjMap.restrictDomain
#check RelativeProjMap.EtaleChartCompatibility
#check RelativeProjMap.theta_isGradedAlgebraMap
