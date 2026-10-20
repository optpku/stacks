/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Pushout
public import ReasLib.RingTheory.RingHom.SquareZero.Pullback
public import ReasLib.RingTheory.RingHom.SquareZero.Functoriality

/-!
# Transport of square-zero algebra extension classes

Coefficient pushouts and base pullbacks compare compatible maps and transport
naive cotangent Ext¹ classes.
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom.SquareZeroExtension

variable {A B C M N : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup N] [Module C N] [Module B N] [Module A N]
variable [IsScalarTower B C N] [IsScalarTower A C N] [IsScalarTower A B N]

/-- A compatible map of square-zero A-algebra extensions exists exactly when
the coefficient pushout and base pullback have the same isomorphism class. -/
theorem exists_fittingMap_iff_isoClass (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M))
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    Nonempty (FittingMap (RelativeDiagram.ofAlgebraMap c SB SC)) ↔
      isoClassMk (pushoutAlong c SB) = isoClassMk (pullbackAlong B SC) := sorry

/-- The Ext¹ class of a coefficient pushout is the image of the original class
under coefficient postcomposition. -/
theorem pushoutAlong_extClass (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    (algebraExtensionEquiv A B N).symm (isoClassMk (pushoutAlong c SB)) =
      extOneNaiveCotangent_map c
        ((algebraExtensionEquiv A B M).symm (isoClassMk SB)) := sorry

/-- The Ext¹ class of a base pullback is the image of the original class
under scalar restriction and cotangent precomposition. -/
theorem pullbackAlong_extClass
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    (algebraExtensionEquiv A B N).symm (isoClassMk (pullbackAlong B SC)) =
      extOneNaiveCotangent_comap B
        ((algebraExtensionEquiv A C N).symm (isoClassMk SC)) := sorry

end SquareZeroExtension

end RingHom
