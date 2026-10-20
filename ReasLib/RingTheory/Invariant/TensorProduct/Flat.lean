module

public import Mathlib.RingTheory.Flat.Equalizer
public import ReasLib.RingTheory.Invariant.TensorProduct

@[expose] public section

/-!
# Flat base change for invariant tensor fixed points

Flatness of the left algebra preserves the equalizer defining the fixed part of a
finite invariant tensor action.  The public result is stated as bijectivity of the
canonical bundled algebra map; callers can construct an equivalence after supplying
the completed proof without committing this owner to a classical inverse datum.

@stack 0BRH
-/

open Algebra.TensorProduct.RightAction
open scoped TensorProduct Algebra.TensorProduct.RightAction

universe u v w x

namespace Algebra.IsInvariant.TensorProduct

variable {S : Type u} {A : Type v} {B : Type w} {G : Type x}
variable [CommRing S] [CommRing A] [CommRing B]
variable [Algebra S A] [Algebra S B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G S B]
variable [Finite G] [Algebra.IsInvariant S B G] [FaithfulSMul S B]

/-- Flat base change makes the canonical map into right-action fixed tensors bijective. -/
@[stacks 0BRH "flat invariant tensor fixed-point map is bijective"]
theorem toFixed_bijective_of_flat [Module.Flat S A] :
    Function.Bijective
      (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom := sorry
-- Proof strategy: install `Fintype.ofFinite G` and express the fixed subring of `B` as the
-- equalizer of the inclusion and the action-difference map `b ↦ (g • b - b)`.  Tensor this
-- exact equalizer sequence on the left by `A`; `Module.Flat.lTensor_exact` preserves exactness,
-- while `TensorProduct.piRight` identifies the finite product after tensoring.  The resulting
-- kernel is exactly `fixedSubalgebra`, and `toFixed` is the tensorized equalizer inclusion.  Use
-- `FaithfulSMul S B` for injectivity and the preserved equalizer for surjectivity.

end Algebra.IsInvariant.TensorProduct
