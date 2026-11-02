/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Finite type morphisms from relative very ampleness

This file records the finite-type consequence of a quasi-compact immersion
into a projective bundle associated to a finite-type module.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- A quasi-compact morphism with a presentation in a projective bundle associated to a
finite-type module is of finite type. -/
theorem RelativelyVeryAmple.finiteType_of_quasiCompact
    {P : Scheme.{u}} (π : P ⟶ S) (ℰ : S.Modules)
    (hπ : Scheme.ProjectiveBundle.Representation π ℰ) (i : X ⟶ P)
    [QuasiCompact f] [ℰ.IsFiniteType]
    (h : RelativelyVeryAmplePresentation f L π ℰ hπ i) :
    Scheme.Hom.FiniteType f := sorry

end AlgebraicGeometry
