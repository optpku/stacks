/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable (C : Type u) [Category.{v} C]

/- Definition 7.47.6: a topology on a category C is an assignment U ↦ J U of
sieves on U such that (1) if f : V ⟶ U and S ∈ J U then S.pullback f ∈ J V,
(2) if S ∈ J U and S' is a sieve on U with S'.pullback f ∈ J V for every
f : V ⟶ U in S, then S' ∈ J U, and (3) the maximal sieve ⊤ belongs to J U.
Covering sieves are the members of J U. This is the canonical owner
GrothendieckTopology. -/
@[stacks 00Z4] #check GrothendieckTopology C

#check @GrothendieckTopology.pullback_stable
#check @GrothendieckTopology.transitive
#check @GrothendieckTopology.top_mem
