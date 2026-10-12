/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.SingleObj.KernelFiber.Counit
public import ReasLib.CategoryTheory.Fibered.SingleObj.KernelFiber.Unit

/-!
# Equivalence between a standard fiber and a one-object kernel

This module assembles the explicit unit and counit comparisons into the canonical equivalence
between the standard fiber of a one-object functor and the one-object category of its kernel.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor Functor.Fiber
open CategoryTheory.SingleObj

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]

namespace KernelFiber

/-- Triangle identity for the explicit fiber-kernel unit and counit. -/
theorem triangle
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    (toKernel p).map
        ((unitIso p).hom.app X) ≫
      (counitIso p).hom.app ((toKernel p).obj X) =
        𝟙 ((toKernel p).obj X) := sorry

/-- The equivalence from the standard fiber of a one-object functor to the one-object category of
the kernel, built from explicit functors in both directions. -/
@[stacks 003U "standard fiber is the kernel one-object groupoid"]
def equivalence (p : G →* H) :
    p.toFunctor.Fiber (star H) ≌ SingleObj p.ker :=
  Equivalence.mk' (toKernel p) (toFiber p) (unitIso p) (counitIso p) (triangle p)

/-- The equivalence from the one-object category of the kernel to the standard fiber, obtained by
reversing the explicit fiber-to-kernel equivalence. -/
def inverseEquivalence (p : G →* H) :
    SingleObj p.ker ≌ p.toFunctor.Fiber (star H) :=
  (equivalence p).symm

/-- The canonical kernel-to-fiber functor is an equivalence. -/
instance toFiber.isEquivalence (p : G →* H) :
    (toFiber p).IsEquivalence := sorry

namespace inverseEquivalence

/-- The forward functor of the kernel-to-fiber equivalence is the explicit kernel inclusion
functor. -/
@[simp]
theorem functor (p : G →* H) :
    (inverseEquivalence p).functor = toFiber p := sorry

end inverseEquivalence

namespace equivalence

/-- The forward functor of the fiber-to-kernel equivalence is the explicit vertical-morphism
extraction functor. -/
@[simp]
theorem functor (p : G →* H) :
    (equivalence p).functor = toKernel p := sorry

/-- The inverse functor of the fiber-to-kernel equivalence is the explicit kernel inclusion
functor. -/
@[simp]
theorem inverse (p : G →* H) :
    (equivalence p).inverse = toFiber p := sorry

/-- The unit isomorphism of `MonoidHom.KernelFiber.equivalence` is the explicit componentwise
unit-element comparison. -/
@[simp]
theorem unitIso (p : G →* H) :
    (equivalence p).unitIso = unitIso p := sorry

/-- The counit isomorphism of `MonoidHom.KernelFiber.equivalence` is the explicit componentwise
unit-element comparison. -/
@[simp]
theorem counitIso (p : G →* H) :
    (equivalence p).counitIso = counitIso p := sorry

end equivalence

end KernelFiber

end MonoidHom
