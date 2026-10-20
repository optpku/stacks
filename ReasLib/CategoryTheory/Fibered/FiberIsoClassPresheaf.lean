/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Cartesian
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Discrete
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.DiscreteTarget
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Equivalence
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Slice

/-!
# Fiberwise isomorphism-class presheaves

Aggregate for the choice-independent fiberwise isomorphism-class presheaf, its cartesian
functoriality, its behavior under equivalence to a discrete fibration, the discrete-fibration
comparison, and the groupoid-target convenience API.
The implementation is deliberately split into small leaves so users can import
only the construction (`Basic`), the cartesian action (`Cartesian`), or the
automatic groupoid-target specialization (`GroupoidTarget`), and concrete fiber-pair slice
presheaves (`Slice`).

The declarations themselves live at datum-oriented owners:
`Functor.fiberIsoClassPresheaf` for the construction,
`CartesianBasedFunctor.fiberIsoClassMap` and `BasedFunctor.fiberIsoClassMap` for
functoriality, `BasedFunctor.fiberClassesMap` for maps into discrete targets, and
`Functor.IsDiscreteFibration.fiberClassesIso` together with
`BasedFunctor.IsEquivalence.fiberClassesIso` for the two comparison isomorphisms.
-/
