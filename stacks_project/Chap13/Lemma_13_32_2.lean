/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.RightDerived
import StacksCheckRecall

@[expose] public section

/-!
# Unbounded right derived functors of finite cohomological dimension

This chapter entry is a source-facing recall of the reusable, construction-independent API.
The source's left exactness hypothesis is represented by `PreservesFiniteLimits F`; its class of
right-acyclic objects is `Functor.RightAcyclic.Bounded F`; and `R^nF = 0` is represented by
`Functor.RightDerived.Bounded.Vanishes.inDegree F n`.
-/

open CategoryTheory ComplexShape

/-
Lemma 13.32.2 (07K7): enough bounded right-acyclic objects and finite cohomological dimension
give an unbounded right derived functor, termwise computation on acyclic complexes, acyclic
replacements, truncation comparison isomorphisms, and cohomological amplitude `[0, n - 1]`.
-/

@[stacks 07K7] #check @Functor.RightAcyclic.Unbounded.everywhereDefined_of_vanishes
#check @Functor.RightAcyclic.Unbounded.Termwise.computesAt
#check @Functor.RightAcyclic.Unbounded.Termwise.existsQuasiIsoTo
#check @Functor.RightDerived.Homotopy.TruncLE.homologyMap_isIso
#check @Functor.RightDerived.Homotopy.TruncLE.homologyIso
#check @Functor.RightAcyclic.Unbounded.Vanishes.TruncGE.homologyMap_isIso
#check @Functor.RightAcyclic.Unbounded.Vanishes.TruncGE.homologyIso
#check @Functor.RightDerived.Homotopy.mapsGE
#check @Functor.RightAcyclic.Unbounded.Vanishes.mapsLE
#check @Functor.RightAcyclic.Unbounded.Vanishes.hasAmplitude
