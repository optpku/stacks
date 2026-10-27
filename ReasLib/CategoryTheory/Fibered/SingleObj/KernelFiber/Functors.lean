/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.SingleObj

/-!
# Functors between a one-object kernel and the standard fiber

This module constructs the two explicit functors relating the one-object category of the kernel
of a group homomorphism to the standard fiber of its induced one-object functor. It also exposes
their basic object and morphism computation API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor Functor.Fiber
open CategoryTheory.SingleObj

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]

namespace KernelFiber

/-- The functor induced by the kernel inclusion becomes constant after composition with the
one-object functor induced by the original group homomorphism. -/
theorem toFiber.comp_const (p : G →* H) :
    (Subgroup.subtype p.ker).toFunctor ⋙ p.toFunctor =
      (const (SingleObj p.ker)).obj (star H) := by
  apply Functor.hext (fun _ ↦ Subsingleton.elim _ _)
  intro X Y f
  exact heq_of_eq (show p (f : p.ker).val = 1 from f.property)

/-- The canonical functor from the one-object category of the kernel to the standard fiber of the
induced one-object functor. -/
def toFiber (p : G →* H) :
    SingleObj p.ker ⥤ p.toFunctor.Fiber (star H) :=
  inducedFunctor (toFiber.comp_const p)

namespace toFiber

/-- Forgetting from the standard fiber after the kernel-to-fiber functor recovers the functor
induced by the kernel inclusion. -/
theorem comp_fiberInclusion (p : G →* H) :
    toFiber p ⋙ fiberInclusion =
      (Subgroup.subtype p.ker).toFunctor :=
  inducedFunctor_comp (toFiber.comp_const p)

/-- Object computation for the kernel-to-fiber functor after forgetting the fiber witness. -/
@[simp]
theorem obj_fiberInclusion
    (p : G →* H) (X : SingleObj p.ker) :
    fiberInclusion.obj ((toFiber p).obj X) =
      (Subgroup.subtype p.ker).toFunctor.obj X :=
  inducedFunctor_comp_obj (toFiber.comp_const p) X

/-- Morphism computation for the kernel-to-fiber functor after forgetting verticality. -/
@[simp]
theorem map_fiberInclusion
    (p : G →* H) {X Y : SingleObj p.ker} (f : X ⟶ Y) :
    fiberInclusion.map ((toFiber p).map f) =
      (Subgroup.subtype p.ker).toFunctor.map f :=
  inducedFunctor_comp_map (toFiber.comp_const p) f

end toFiber

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The underlying group element of a vertical fiber morphism belongs to the kernel. -/
private theorem fiberMap_mem_ker
    (p : G →* H) {X Y : p.toFunctor.Fiber (star H)} (f : X ⟶ Y) :
    p (fiberInclusion.map f) = 1 := by
  exact (@IsHomLift.eq_of_isHomLift _ _ _ _ p.toFunctor X.1 Y.1
    (𝟙 (star H)) (fiberInclusion.map f) f.property).symm

/-- Extract the kernel element represented by a vertical fiber morphism. -/
private def fiberToKernelMap
    (p : G →* H) {X Y : p.toFunctor.Fiber (star H)} (f : X ⟶ Y) :
    p.ker :=
  ⟨fiberInclusion.map f, fiberMap_mem_ker p f⟩

/-- Extraction of a kernel element preserves identity morphisms. -/
private theorem fiberToKernelMap_id
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    fiberToKernelMap p (𝟙 X) = 𝟙 (star p.ker) :=
  Subtype.ext rfl

/-- Extraction of kernel elements preserves composition. -/
private theorem fiberToKernelMap_comp
    (p : G →* H) {X Y Z : p.toFunctor.Fiber (star H)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberToKernelMap p (f ≫ g) =
      fiberToKernelMap p g * fiberToKernelMap p f :=
  Subtype.ext rfl

end Implementation

/-- The explicit functor from the standard fiber of a one-object functor to the one-object
category of the kernel. On morphisms it retains the underlying group element and uses verticality
as its kernel-membership proof. -/
def toKernel (p : G →* H) :
    p.toFunctor.Fiber (star H) ⥤ SingleObj p.ker where
  obj _ := star p.ker
  map := Implementation.fiberToKernelMap p
  map_id := Implementation.fiberToKernelMap_id p
  map_comp := Implementation.fiberToKernelMap_comp p

namespace toKernel

/-- The fiber-to-kernel functor is constant on the unique object of the one-object target. -/
@[simp]
theorem obj
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    (toKernel p).obj X = star p.ker := rfl

/-- The fiber-to-kernel functor sends a vertical morphism to its underlying group element. -/
@[simp]
theorem map_val
    (p : G →* H) {X Y : p.toFunctor.Fiber (star H)} (f : X ⟶ Y) :
    ((toKernel p).map f : p.ker).1 =
      fiberInclusion.map f := rfl

end toKernel

end KernelFiber

end MonoidHom
