module

public import ReasLib.CategoryTheory.Fibered.SingleObj.KernelFiber.Functors

/-!
# Counit of the standard fiber-kernel equivalence

This module constructs the objectwise counit comparison and packages it as a natural isomorphism.
Its component lemmas make the unit element of the kernel visible to downstream computations.
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

/-- The forward counit component, explicitly given by the unit of `p.ker`. -/
private def fiberToKernelCounitHom
    (p : G →* H) (X : SingleObj p.ker) :
    (toKernel p).obj ((toFiber p).obj X) ⟶ X :=
  (1 : p.ker)

/-- The inverse counit component, explicitly given by the unit of `p.ker`. -/
private def fiberToKernelCounitInv
    (p : G →* H) (X : SingleObj p.ker) :
    X ⟶ (toKernel p).obj ((toFiber p).obj X) :=
  (1 : p.ker)

/-- The forward and inverse unit elements of `p.ker` compose to the identity on the source of
the fibre-kernel counit. -/
private theorem fiberToKernelCounitHomInv
    (p : G →* H) (X : SingleObj p.ker) :
    fiberToKernelCounitHom p X ≫ fiberToKernelCounitInv p X =
      𝟙 ((toKernel p).obj ((toFiber p).obj X)) := sorry

/-- The inverse and forward unit elements of `p.ker` compose to the identity on the target of
the fibre-kernel counit. -/
private theorem fiberToKernelCounitInvHom
    (p : G →* H) (X : SingleObj p.ker) :
    fiberToKernelCounitInv p X ≫ fiberToKernelCounitHom p X =
      𝟙 X := sorry

end Implementation

/-- The objectwise counit isomorphism of the explicit fibre-kernel equivalence. Both directions
are the unit element of the kernel group. -/
def counitIsoApp
    (p : G →* H) (X : SingleObj p.ker) :
    (toKernel p).obj ((toFiber p).obj X) ≅ X where
  hom := Implementation.fiberToKernelCounitHom p X
  inv := Implementation.fiberToKernelCounitInv p X
  hom_inv_id := Implementation.fiberToKernelCounitHomInv p X
  inv_hom_id := Implementation.fiberToKernelCounitInvHom p X

namespace counitIsoApp

/-- The forward fibre-kernel counit component is the unit element of `p.ker`. -/
@[simp]
theorem hom
    (p : G →* H) (X : SingleObj p.ker) :
    (counitIsoApp p X).hom = (1 : p.ker) := sorry

/-- The inverse fibre-kernel counit component is the unit element of `p.ker`. -/
@[simp]
theorem inv
    (p : G →* H) (X : SingleObj p.ker) :
    (counitIsoApp p X).inv = (1 : p.ker) := sorry

/-- The explicit counit components are natural in morphisms of the one-object kernel
groupoid. -/
theorem naturality
    (p : G →* H) {X Y : SingleObj p.ker} (f : X ⟶ Y) :
    (toFiber p ⋙ toKernel p).map f ≫
        (counitIsoApp p Y).hom =
    (counitIsoApp p X).hom ≫ f := sorry

end counitIsoApp

/-- Explicit counit natural isomorphism for the fibre-to-kernel equivalence. -/
def counitIso (p : G →* H) :
    toFiber p ⋙ toKernel p ≅
      𝟭 (SingleObj p.ker) :=
  NatIso.ofComponents (counitIsoApp p) (fun f ↦ counitIsoApp.naturality p f)

end KernelFiber

end MonoidHom
