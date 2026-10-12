/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.SingleObj.KernelFiber.Functors

/-!
# Unit of the standard fiber-kernel equivalence

This module constructs the objectwise unit comparison and packages it as a natural isomorphism.
The computation lemmas expose its underlying vertical morphisms for downstream use.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor Functor.Fiber
open CategoryTheory.SingleObj

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]

namespace KernelFiber

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The unit element of `G`, viewed as the forward vertical component of the fibre-kernel
comparison, lies over the identity of the unique object of `SingleObj H`. -/
private theorem fiberToKernelUnitHom_isHomLift
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    p.toFunctor.IsHomLift (𝟙 (star H))
      (1 : X.1 ⟶
        ((toFiber p).obj ((toKernel p).obj X)).1) := sorry

/-- The explicit forward vertical component of the fibre-kernel unit. -/
private def fiberToKernelUnitHom
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    X ⟶ (toFiber p).obj ((toKernel p).obj X) :=
  ⟨1, fiberToKernelUnitHom_isHomLift p X⟩

/-- The unit element of `G`, viewed in the reverse direction, is again vertical over the
identity of the unique base object. -/
private theorem fiberToKernelUnitInv_isHomLift
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    p.toFunctor.IsHomLift (𝟙 (star H))
      (1 :
        ((toFiber p).obj ((toKernel p).obj X)).1 ⟶ X.1) := sorry

/-- The explicit inverse vertical component of the fibre-kernel unit. -/
private def fiberToKernelUnitInv
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    (toFiber p).obj ((toKernel p).obj X) ⟶ X :=
  ⟨1, fiberToKernelUnitInv_isHomLift p X⟩

/-- The two explicit unit-element components compose to the identity on the source fibre
object. -/
private theorem fiberToKernelUnitHomInv
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    fiberToKernelUnitHom p X ≫ fiberToKernelUnitInv p X = 𝟙 X := sorry

/-- The two explicit unit-element components compose to the identity on the reconstructed fibre
object. -/
private theorem fiberToKernelUnitInvHom
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    fiberToKernelUnitInv p X ≫ fiberToKernelUnitHom p X =
      𝟙 ((toFiber p).obj ((toKernel p).obj X)) := sorry

end Implementation

/-- The objectwise unit isomorphism of the explicit fibre-kernel equivalence. Both directions
are the unit element of `G`; only their verticality and inverse laws are proof fields. -/
def unitIsoApp
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    X ≅ (toFiber p).obj ((toKernel p).obj X) where
  hom := Implementation.fiberToKernelUnitHom p X
  inv := Implementation.fiberToKernelUnitInv p X
  hom_inv_id := Implementation.fiberToKernelUnitHomInv p X
  inv_hom_id := Implementation.fiberToKernelUnitInvHom p X

namespace unitIsoApp

/-- Forgetting verticality from the forward fibre-kernel unit component gives the unit element
of `G`. -/
@[simp]
theorem hom_fiberInclusion
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    fiberInclusion.map (unitIsoApp p X).hom =
      (1 : X.1 ⟶
        ((toFiber p).obj ((toKernel p).obj X)).1) := sorry

/-- Forgetting verticality from the inverse fibre-kernel unit component gives the unit element
of `G`. -/
@[simp]
theorem inv_fiberInclusion
    (p : G →* H) (X : p.toFunctor.Fiber (star H)) :
    fiberInclusion.map (unitIsoApp p X).inv =
      (1 :
        ((toFiber p).obj ((toKernel p).obj X)).1 ⟶ X.1) := sorry

/-- The explicit unit components are natural in vertical morphisms of the standard fibre. -/
theorem naturality
    (p : G →* H) {X Y : p.toFunctor.Fiber (star H)} (f : X ⟶ Y) :
    f ≫ (unitIsoApp p Y).hom =
      (unitIsoApp p X).hom ≫
        (toKernel p ⋙ toFiber p).map f := sorry

end unitIsoApp

/-- Explicit unit natural isomorphism for the fibre-to-kernel equivalence. -/
def unitIso (p : G →* H) :
    𝟭 (p.toFunctor.Fiber (star H)) ≅
      toKernel p ⋙ toFiber p :=
  NatIso.ofComponents (unitIsoApp p) (fun f ↦ unitIsoApp.naturality p f)

end KernelFiber

end MonoidHom
