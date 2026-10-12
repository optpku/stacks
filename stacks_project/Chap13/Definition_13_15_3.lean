/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived
import StacksCheckRecall

@[expose] public section

/-!
# Derived functors and acyclic objects

The reusable API models acyclicity by the statement that the degree-zero complex computes the
appropriate derived functor.  Bounded and unbounded variants are distinguished by namespaces,
not by repeating the ambient construction in one declaration name.
-/

open CategoryTheory ComplexShape

/-
Definition 13.15.3 (0157): right and left derived functors are the corresponding partial derived
functors, and an object is acyclic when its degree-zero complex computes that derived functor.
-/

@[stacks 0157] #check @Functor.RightDerived.Bounded.functor
#check @Functor.RightDerived.Bounded.unit
#check @Functor.RightDerived.Bounded.zero
#check @Functor.RightDerived.Bounded.map
#check @Functor.RightDerived.Bounded.mapIso
#check @Functor.RightDerived.Bounded.degree.map
#check @Functor.RightDerived.Bounded.degree.mapIso
#check @Functor.RightDerived.degree.modelFunctor
#check @Functor.RightDerived.degree.fromHomotopy.modelFunctor
#check @Functor.RightDerived.degree.fromHomotopy.iso
#check @Functor.RightDerived.Bounded.zero_naturality
#check @Functor.RightDerived.Bounded.fromCochainMap
#check @Functor.LeftDerived.Bounded.functor
#check @Functor.LeftDerived.Bounded.counit
#check @Functor.LeftDerived.Bounded.zero
#check @Functor.LeftDerived.Bounded.map
#check @Functor.LeftDerived.Bounded.mapIso
#check @Functor.LeftDerived.Bounded.degree.map
#check @Functor.LeftDerived.Bounded.degree.mapIso
#check @Functor.LeftDerived.degree.modelFunctor
#check @Functor.LeftDerived.degree.fromHomotopy.modelFunctor
#check @Functor.LeftDerived.degree.fromHomotopy.iso
#check @Functor.LeftDerived.Bounded.homologicalDegree.map
#check @Functor.LeftDerived.Bounded.homologicalDegree.mapIso
#check @Functor.LeftDerived.homologicalDegree.modelFunctor
#check @Functor.LeftDerived.homologicalDegree.fromHomotopy.modelFunctor
#check @Functor.LeftDerived.homologicalDegree.fromHomotopy.iso
#check @Functor.LeftDerived.Bounded.zero_naturality
#check @Functor.LeftDerived.Bounded.fromCochainMap
#check @Functor.LeftDerived.degree
#check @Functor.LeftDerived.homologicalDegree
#check @Functor.LeftDerived.Bounded.homologicalDegree
#check @Functor.LeftDerived.Bounded.zero.preservesFiniteColimits
#check @Functor.RightAcyclic.Bounded
#check @Functor.RightAcyclic.Bounded.Termwise
#check @Functor.RightAcyclic
#check @Functor.RightAcyclic.Termwise
#check @Functor.LeftAcyclic.Bounded
#check @Functor.LeftAcyclic.Bounded.Termwise
#check @Functor.LeftAcyclic
#check @Functor.LeftAcyclic.Termwise
#check @HomotopyCategory.Plus.singleFunctor
#check @HomotopyCategory.Minus.singleFunctor
