/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Sites.Spaces
import ReasLib.Topology.Opens.Site
import StacksCheckRecall

open CategoryTheory TopologicalSpace CategoryTheory.Limits

/- Example 59.10.3: for a topological space `X`, the category of open subsets with inclusion
morphisms, the usual open-covering families, and pullbacks represented by intersections are
the canonical opens-site constructions. -/
@[stacks 03NI] #check
  (TopologicalSpace.Opens.pullback_coe_eq_intersection :
    ∀ {T : Type*} [TopologicalSpace T] {U V W : Opens T}
      (f : U ⟶ W) (g : V ⟶ W),
      (pullback f g : Set T) = (U : Set T) ∩ (V : Set T))

#check
  (Opens.pretopology : ∀ (T : Type*) [TopologicalSpace T], Pretopology (Opens T))

#check
  (Opens.grothendieckTopology :
    ∀ (T : Type*) [TopologicalSpace T], GrothendieckTopology (Opens T))

#check
  (Opens.pretopology_toGrothendieck :
    ∀ (T : Type*) [TopologicalSpace T],
      (Opens.pretopology T).toGrothendieck = Opens.grothendieckTopology T)

#check
  (Opens.coversTop_iff :
    ∀ (T : Type*) [TopologicalSpace T] {ι : Type*} (U : ι → Opens T),
      (Opens.grothendieckTopology T).CoversTop U ↔ IsOpenCover U)

#check
  (CategoryTheory.Limits.CompleteLattice.pullback_eq_inf :
    ∀ {T : Type*} [TopologicalSpace T] {U V W : Opens T}
      (f : U ⟶ W) (g : V ⟶ W), pullback f g = U ⊓ V)

#check
  (Opens.coe_inf :
    ∀ {T : Type*} [TopologicalSpace T] (U V : Opens T),
      (U ⊓ V : Set T) = (U : Set T) ∩ (V : Set T))
