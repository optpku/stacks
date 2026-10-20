/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.Neighborhood
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.Neighborhood
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite Free Neighborhoods from Fibrewise Flatness

This file gives a finite-free neighborhood criterion for finitely presented module sheaves on
schemes in terms of relative flatness and flatness on a scheme-theoretic fibre.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module sheaf that is flat over the base at a point and whose
restriction to the scheme-theoretic fibre is flat at the corresponding fibre point is finite
free on an open neighborhood of that point. -/
theorem existsNeighborhoodFree_of_flatnessByFibers {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (h_flat : flatOverAt F f x)
    (h_fiber : SheafOfModules.IsFlatAt
      ((pullback (f.fiberι (f x))).obj F) (f.asFiber x)) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty (F.over U ≅ SheafOfModules.free.{u} I) := sorry

end AlgebraicGeometry.Scheme.Modules
