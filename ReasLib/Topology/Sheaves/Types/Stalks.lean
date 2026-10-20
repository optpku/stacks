/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of dependent-function sheaves

This module exposes the evaluation map from the stalk of the sheaf of dependent functions to a
fiber.  The sheaf `TopCat.sheafToTypes` remains the data owner; the constructions here are its
stalkwise evaluation API.  Mathlib's `TopCat.stalkToFiber` is the more general construction for
local-predicate subsheaves, but its sections are subtype-valued and are not definitionally the
sections of `sheafToTypes`; this file is the direct all-functions specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat

variable {X : TopCat.{u}} (A : X → Type u) (x : X)

/-- Evaluation at `x` on sections over one open neighborhood of `x`. -/
def dependentFunctionStalkToFiberLeg (U : (OpenNhds x)ᵒᵖ) :
    ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf).obj U ⟶ A x :=
  ↾fun f ↦ f ⟨x, (unop U).2⟩

/-- Evaluation at a point is compatible with restriction between its open neighborhoods. -/
theorem dependentFunctionStalkToFiberLeg_naturality {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf).map i) ≫
        dependentFunctionStalkToFiberLeg A x V =
      dependentFunctionStalkToFiberLeg A x U := sorry

/-- The cocone that evaluates a dependent function defined near `x` at the point `x`. -/
def dependentFunctionStalkToFiberCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf) where
  pt := A x
  ι :=
    { app U := dependentFunctionStalkToFiberLeg A x U
      naturality := fun _ _ i ↦ dependentFunctionStalkToFiberLeg_naturality A x i }

/-- Evaluation from the stalk of the dependent-function sheaf at `x` to the fiber `A x`. -/
def dependentFunctionStalkToFiber :
    (X.sheafToTypes A).presheaf.stalk x ⟶ A x :=
  colimit.desc _ (dependentFunctionStalkToFiberCocone A x)

/-- Evaluating the germ of a dependent function recovers its value at the chosen point. -/
theorem dependentFunctionStalkToFiber_germ (U : Opens X) (hx : x ∈ U)
    (f : (X.sheafToTypes A).presheaf.obj (op U)) :
    dependentFunctionStalkToFiber A x ((X.sheafToTypes A).presheaf.germ U x hx f) =
      f ⟨x, hx⟩ := sorry

/-- If every open neighborhood of `x` contains a point with an empty fiber, then the stalk at
`x` of the dependent-function sheaf is empty. -/
theorem isEmpty_stalk_of_exists_empty_fiber_in_every_openNhds
    (h : ∀ U : OpenNhds x, ∃ y : U.1, IsEmpty (A y)) :
    IsEmpty ((X.sheafToTypes A).presheaf.stalk x) := sorry

end TopCat
