/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Localization
public import ReasLib.RingTheory.RingHom.Local.AtPrime

/-!
# Tensor Products with a Local Target

This leaf packages the prime of a tensor product selected by two maps into a
common local target.  The underlying tensor map is Mathlib's
`Algebra.TensorProduct.productMap`; the additions here are the local-target
point, its contractions, and its explicitly controlled localization map.

@stack 08HU
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Algebra.TensorProduct.LocalTarget

variable {R : Type u} {A : Type v} {B : Type w} {T : Type x}

section Local

variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring T]
variable [Algebra R A] [Algebra R B] [Algebra R T]
variable [IsLocalRing T]

/-- The prime of `A ⊗[R] B` obtained by pulling the closed point of
the local target `T` back along `Algebra.TensorProduct.productMap`. -/
@[stacks 08HU "local-target prime of a tensor product"]
def tensorPrime (f : A →ₐ[R] T) (g : B →ₐ[R] T) : PrimeSpectrum (A ⊗[R] B) :=
  PrimeSpectrum.comap (Algebra.TensorProduct.productMap f g).toRingHom
    (IsLocalRing.closedPoint T)

/-- The left restriction of `tensorPrime` is the pullback of the
closed point of `T` along the left input map. -/
@[stacks 08HU "left restriction of the local-target tensor prime"]
theorem tensorPrime_restrictLeft (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)
        (tensorPrime f g) =
      PrimeSpectrum.comap f.toRingHom (IsLocalRing.closedPoint T) := sorry

/-- The right restriction of `tensorPrime` is the pullback of the
closed point of `T` along the right input map. -/
@[stacks 08HU "right restriction of the local-target tensor prime"]
theorem tensorPrime_restrictRight (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (tensorPrime f g) =
      PrimeSpectrum.comap g.toRingHom (IsLocalRing.closedPoint T) := sorry

/-- The ideal underlying `tensorPrime` is the contraction of the
maximal ideal of `T` along `Algebra.TensorProduct.productMap`. -/
@[simp, stacks 08HU "ideal of the local-target tensor prime"]
theorem tensorPrime_asIdeal (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    (tensorPrime f g).asIdeal =
      Ideal.comap (Algebra.TensorProduct.productMap f g).toRingHom
        (IsLocalRing.maximalIdeal T) := sorry

/-- Contracting `tensorPrime` along the left tensor inclusion gives
the contraction of the maximal ideal of `T` along the left input map. -/
@[stacks 08HU "left contraction of the local-target tensor prime"]
theorem tensorPrime_comap_includeLeft (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    Ideal.comap
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)
        (tensorPrime f g).asIdeal =
      Ideal.comap f.toRingHom (IsLocalRing.maximalIdeal T) := sorry

/-- Contracting `tensorPrime` along the right tensor inclusion gives
the contraction of the maximal ideal of `T` along the right input map. -/
@[stacks 08HU "right contraction of the local-target tensor prime"]
theorem tensorPrime_comap_includeRight (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    Ideal.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (tensorPrime f g).asIdeal =
      Ideal.comap g.toRingHom (IsLocalRing.maximalIdeal T) := sorry

/-- If the left input map is local, the left restriction of
`tensorPrime` is the closed point of `A`. -/
@[stacks 08HU "local left restriction of the tensor prime"]
theorem tensorPrime_restrictLeft_eq_closedPoint
    (f : A →ₐ[R] T) (g : B →ₐ[R] T)
    [IsLocalRing A] [IsLocalHom f.toRingHom] :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)
        (tensorPrime f g) =
      IsLocalRing.closedPoint A := sorry

/-- If the right input map is local, the right restriction of
`tensorPrime` is the closed point of `B`. -/
@[stacks 08HU "local right restriction of the tensor prime"]
theorem tensorPrime_restrictRight_eq_closedPoint
    (f : A →ₐ[R] T) (g : B →ₐ[R] T)
    [IsLocalRing B] [IsLocalHom g.toRingHom] :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (tensorPrime f g) =
      IsLocalRing.closedPoint B := sorry

/-- The map from the localization of the tensor product at
`tensorPrime` to the local target. A local commutative semiring is
canonically its own localization at the complement of its maximal ideal; that proof-only
localization structure is supplied by the shared contracted-point owner. -/
@[stacks 08HU "localized map from the local-target tensor prime"]
noncomputable def localizedMap (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    Localization.AtPrime (tensorPrime f g).asIdeal →+* T :=
  RingHom.LocalTarget.mapAtClosedPoint (Algebra.TensorProduct.productMap f g).toRingHom

/-- `localizedMap` extends `Algebra.TensorProduct.productMap` across localization at
`tensorPrime`. -/
@[stacks 08HU "localized map extends the tensor-product map"]
theorem localizedMap_algebraMap (f : A →ₐ[R] T) (g : B →ₐ[R] T)
    (x : A ⊗[R] B) :
    localizedMap f g
        (algebraMap (A ⊗[R] B)
          (Localization.AtPrime (tensorPrime f g).asIdeal) x) =
      Algebra.TensorProduct.productMap f g x := sorry

/-- After localizing at `tensorPrime`, the map to the target still
restricts on the left to the original left input map. -/
@[stacks 08HU "left restriction after tensor localization"]
theorem localizedMap_comp_includeLeft (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    (localizedMap f g).comp
        ((algebraMap (A ⊗[R] B)
            (Localization.AtPrime (tensorPrime f g).asIdeal)).comp
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) =
      f.toRingHom := sorry

/-- After localizing at `tensorPrime`, the map to the target still
restricts on the right to the original right input map. -/
@[stacks 08HU "right restriction after tensor localization"]
theorem localizedMap_comp_includeRight (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    (localizedMap f g).comp
        ((algebraMap (A ⊗[R] B)
            (Localization.AtPrime (tensorPrime f g).asIdeal)).comp
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      g.toRingHom := sorry

/-- The localization map from `tensorPrime` to the local target is
a local homomorphism. -/
@[stacks 08HU "locality of the localized tensor map"]
theorem localizedMap_isLocalHom (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    IsLocalHom (localizedMap f g) := sorry

/-- The explicitly named algebra structure on the localization at
`tensorPrime` with target `T`.  It is a named definition rather than a global
instance, because it depends on the selected maps into the local target. -/
@[reducible, stacks 08HU "localized algebra structure for the tensor target"]
noncomputable def localizedAlgebra (f : A →ₐ[R] T) (g : B →ₐ[R] T) :
    Algebra (Localization.AtPrime (tensorPrime f g).asIdeal) T :=
  RingHom.toAlgebra (localizedMap f g)

end Local

end Algebra.TensorProduct.LocalTarget
