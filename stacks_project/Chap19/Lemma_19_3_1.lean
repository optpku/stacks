/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Injective
import StacksCheckRecall

/-!
# Lemma 19.3.1 compatibility facade

The algebraic cofree action and the open-stabilizer coreflection are owned by ReasLib.  This file
retains the source-facing Chapter 19 statements.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open scoped Topology

universe u v

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Lemma 19.3.1: `DiscreteModuleCat R G`, the category of discrete `R`-modules with continuous
`G`-action, has functorial injective embeddings. -/
@[stacks 04JF "discrete R-G modules"]
#check (inferInstance : HasFunctorialInjectives (DiscreteModuleCat R G))

/- Lemma 19.3.1, in particular: the category of discrete `G`-modules has functorial injective
embeddings, by specializing to `R = ℤ`. -/
@[stacks 04JF "discrete G-modules"]
#check (inferInstance : HasFunctorialInjectives (DiscreteModuleCat ℤ G))
