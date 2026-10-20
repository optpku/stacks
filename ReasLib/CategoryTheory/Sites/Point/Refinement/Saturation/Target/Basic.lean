/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Request
public import ReasLib.CategoryTheory.Sites.Point.Refinement.System.Basic

/-!
# Finite-cover saturation targets

This leaf owns the source-free objects of finite-cover saturation.  A `Target`
is a directed preorder system together with exactly the smallness and colimit
support needed for its presheaf fiber.  Source-free target refinements and their
category structure are supplied separately by `Target.Category`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]

/-- A directed system equipped with the support needed to ask and solve finite-cover
lifting requests on its presheaf fiber. -/
structure Target (C : Type u) [Category.{v} C] [LocallySmall.{q} C] where
  /-- The possibly empty directed preorder system at the target of a refinement. -/
  system : DirectedPreorderSystem.{u, v, r} C
  /-- Essential smallness of the target index in the fiber universe. -/
  indexEssentiallySmall : EssentiallySmall.{q} system.indexᵒᵖ
  /-- Colimits used to form the target presheaf fiber. -/
  presheafFiberHasColimits :
    letI : EssentiallySmall.{q} system.indexᵒᵖ := indexEssentiallySmall
    HasColimitsOfShape
      (EssentiallySmallFiber.fiber system.diagram).Elementsᵒᵖ (Type q)

namespace Target

variable [LocallySmall.{q} C]

/-- Package a directed preorder system as a saturation target using the ambient smallness and
presheaf-fiber colimit instances. -/
noncomputable def of (system : DirectedPreorderSystem.{u, v, r} C)
    [EssentiallySmall.{q} system.indexᵒᵖ]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber system.diagram).Elementsᵒᵖ (Type q)] :
    Target.{u, v, q, r} C where
  system := system
  indexEssentiallySmall := inferInstance
  presheafFiberHasColimits := inferInstance

/-- The directed preorder system underlying `Target.of system` is `system`. -/
@[simp]
theorem of.system (system : DirectedPreorderSystem.{u, v, r} C)
    [EssentiallySmall.{q} system.indexᵒᵖ]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber system.diagram).Elementsᵒᵖ (Type q)] :
    (of system).system = system := sorry

/-- The target index carries its packaged essential-smallness instance. -/
instance instIndexEssentiallySmall (T : Target.{u, v, q, r} C) :
    EssentiallySmall.{q} T.system.indexᵒᵖ :=
  T.indexEssentiallySmall

/-- The target presheaf fiber carries its packaged colimit instance. -/
instance instFiberHasColimits (T : Target.{u, v, q, r} C) :
    HasColimitsOfShape
      (EssentiallySmallFiber.fiber T.system.diagram).Elementsᵒᵖ (Type q) :=
  T.presheafFiberHasColimits

/-- The inverse-system diagram carried by a saturation target. -/
abbrev diagram (T : Target.{u, v, q, r} C) : T.system.indexᵒᵖ ⥤ C :=
  T.system.diagram

/-- The inverse-system diagram underlying `Target.of system` is the diagram of `system`. -/
@[simp]
theorem of.diagram (system : DirectedPreorderSystem.{u, v, r} C)
    [EssentiallySmall.{q} system.indexᵒᵖ]
    [HasColimitsOfShape
      (EssentiallySmallFiber.fiber system.diagram).Elementsᵒᵖ (Type q)] :
    (of system).diagram = system.diagram := sorry

/-- Saturation targets are determined by their underlying directed preorder
system; the remaining fields are proposition-valued support data. -/
@[ext]
theorem ext {A B : Target.{u, v, q, r} C} (h_system : A.system = B.system) :
    A = B := sorry

/-- The object fiber carried by a saturation target. -/
noncomputable abbrev fiber (T : Target.{u, v, q, r} C) : C ⥤ Type q :=
  EssentiallySmallFiber.fiber T.diagram

/-- A finite-cover lifting request on the fiber of a saturation target. -/
noncomputable abbrev Request (T : Target.{u, v, q, r} C)
    (J : GrothendieckTopology C) : Type (max u v q) :=
  EssentiallySmallFiber.CoverLift.Request J T.diagram

/-- Completion of a saturation target means realization of every finite-cover request on its
fiber.  This property does not depend on a chosen source refinement or scheduling policy. -/
def complete (T : Target.{u, v, q, r} C) (J : GrothendieckTopology C) : Prop :=
  ∀ request : T.Request J, request.is_realized

/-- Target completion is equivalent to finite-cover lifting for its fiber, in every cover-family
universe `w'`. -/
theorem complete_iff_finiteCoverLifts (T : Target.{u, v, q, r} C)
    (J : GrothendieckTopology C) :
    T.complete J ↔ Functor.FiniteCoverLifts.{u, v, q, w'} T.fiber J := sorry

end Target
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
