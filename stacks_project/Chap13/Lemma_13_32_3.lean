module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.LeftDerived
import StacksCheckRecall

@[expose] public section

/-!
# Unbounded left derived functors of finite homological dimension

This chapter entry is a source-facing recall of the reusable, construction-independent API.
The source's right exactness hypothesis is represented by `PreservesFiniteColimits F`; its class
of left-acyclic objects is `Functor.LeftAcyclic.Bounded F`; the textbook's homological degree
`LₙF` is `Functor.LeftDerived.Bounded.homologicalDegree F n = H⁻ⁿ(LF)`; and its vanishing is
`Functor.LeftDerived.Bounded.Vanishes.inDegree F n`.
-/

open CategoryTheory ComplexShape

/-
Lemma 13.32.3 (07K8): enough bounded left-acyclic objects and finite homological dimension give
an unbounded left derived functor, termwise computation on acyclic complexes, acyclic
coreplacements, truncation comparison isomorphisms, and cohomological amplitude `[1 - n, 0]`.
-/

@[stacks 07K8] #check @Functor.LeftAcyclic.Unbounded.everywhereDefined_of_vanishes
#check @Functor.LeftAcyclic.Unbounded.Termwise.computesAt
#check @Functor.LeftAcyclic.Unbounded.Termwise.existsQuasiIsoFrom
#check @Functor.LeftAcyclic.Unbounded.Vanishes.TruncLE.homologyMap_isIso
#check @Functor.LeftAcyclic.Unbounded.Vanishes.TruncLE.homologyIso
#check @Functor.LeftDerived.Homotopy.TruncGE.homologyMap_isIso
#check @Functor.LeftDerived.Homotopy.TruncGE.homologyIso
#check @Functor.LeftAcyclic.Unbounded.Vanishes.mapsGE
#check @Functor.LeftDerived.Homotopy.mapsLE
#check @Functor.LeftAcyclic.Unbounded.Vanishes.hasAmplitude
