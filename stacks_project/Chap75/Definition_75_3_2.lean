/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
import Mathlib.Topology.Sets.Closeds
import stacks_project.Chap66.Lemma_66_4_6_Topology
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open TopologicalSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (E : ModuleDerived X)
variable (T : Closeds (Points X))

/- Definition 75.3.2: `E` is supported on the closed subset `T` when all of its
cohomology sheaves are supported on `T`. -/
@[stacks 08GF] #check (IsSupportedOn E (T : Set (Points X)) : Prop)

/- The canonical predicate is equivalent to the support condition in every cohomological degree. -/
#check isSupportedOn_iff E (T : Set (Points X))
