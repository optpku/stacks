/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Basis.Cofinal
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X] {B : Set (Opens X)}

/- Lemma 6.30.3: a presheaf of sets on a topological basis is a sheaf on the basis if and only if
it satisfies the basis sheaf condition `(**)` for every cover in a chosen cofinal system, using the
given covers of pairwise intersections. -/
@[stacks 009K]
#check
  CategoryTheory.Presheaf.isBasisSheaf_iff_hasSheafCondition_on_cofinalSystem
    (X := X) (B := B)
