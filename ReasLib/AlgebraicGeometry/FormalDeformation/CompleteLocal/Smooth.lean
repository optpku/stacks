/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.Algebra.Algebra.ResidueImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Classical
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.RingTheory.Smooth.Adic.Basic

/-!
# Smoothness criteria for complete local algebras

Smoothness of restricted coyoneda is equivalent to maximal-adic formal
smoothness and flat closed-fiber criteria over the image field of the base.
Over a classical base it is also equivalent to a power series presentation.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped TensorProduct

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The special fiber has the canonical algebra structure from its right tensor factor. -/
instance instAlgebra_specialFiber (R : CompleteLocalAlgCat Λ k) :
    Algebra (Algebra.residueImage Λ k) (R.carrier ⊗[Λ] Algebra.residueImage Λ k) :=
  Algebra.TensorProduct.rightAlgebra

/-- The special-fiber adic ideal is the extension of the complete local algebra's maximal ideal. -/
def specialFiberAdicIdeal (R : CompleteLocalAlgCat Λ k) :
    Ideal (R.carrier ⊗[Λ] Algebra.residueImage Λ k) :=
  Ideal.map Algebra.TensorProduct.includeLeftRingHom (IsLocalRing.maximalIdeal R.carrier)

/-- The special-fiber adic ideal is computed by mapping the maximal ideal along the left inclusion. -/
theorem specialFiberAdicIdeal_eq (R : CompleteLocalAlgCat Λ k) :
    specialFiberAdicIdeal R =
      Ideal.map Algebra.TensorProduct.includeLeftRingHom (IsLocalRing.maximalIdeal R.carrier) :=
  rfl

/-- Smoothness of restricted coyoneda, maximal-adic formal smoothness, flatness with
geometrically regular special fiber, and flatness with formally smooth special fiber
are equivalent for a complete local algebra. -/
theorem isSmooth_tfae (R : CompleteLocalAlgCat Λ k) :
    List.TFAE
      [Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)),
        (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier),
        (algebraMap Λ R.carrier).Flat ∧
          Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k),
        (algebraMap Λ R.carrier).Flat ∧
          (algebraMap (Algebra.residueImage Λ k)
              (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
            (specialFiberAdicIdeal R)] :=
  sorry

/-- Smoothness of restricted coyoneda is equivalent to maximal-adic formal smoothness
of the structure map of a complete local algebra. -/
theorem isSmooth_iff_formallySmooth (R : CompleteLocalAlgCat Λ k) :
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)) ↔
      (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier) :=
  sorry

/-- Maximal-adic formal smoothness is equivalent to flatness and geometric regularity
of the special fiber over the image field of the base. -/
theorem formallySmooth_iff_flat_isGeometricallyRegular (R : CompleteLocalAlgCat Λ k) :
    (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier) ↔
      (algebraMap Λ R.carrier).Flat ∧
        Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
          (R.carrier ⊗[Λ] Algebra.residueImage Λ k) :=
  sorry

/-- Maximal-adic formal smoothness is equivalent to flatness and adic formal
smoothness of the special fiber over the image field of the base. -/
theorem formallySmooth_iff_flat_formallySmooth_specialFiber
    (R : CompleteLocalAlgCat Λ k) :
    (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier) ↔
      (algebraMap Λ R.carrier).Flat ∧
        (algebraMap (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
          (specialFiberAdicIdeal R) :=
  sorry

/-- Over a classical base, the four smoothness criteria for a complete local algebra
are also equivalent to a finite-variable power series presentation over the base. -/
theorem isSmooth_tfae_isClassical [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    List.TFAE
      [Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)),
        (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier),
        (algebraMap Λ R.carrier).Flat ∧
          Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k),
        (algebraMap Λ R.carrier).Flat ∧
          (algebraMap (Algebra.residueImage Λ k)
              (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
            (specialFiberAdicIdeal R),
        IsPowerSeriesOver (fromClassical R)] :=
  sorry

/-- Over a classical base, smoothness of restricted coyoneda is equivalent to
a finite-variable power series presentation over the base. -/
theorem isSmooth_iff_isPowerSeriesOver [IsClassical Λ k]
    (R : CompleteLocalAlgCat Λ k) :
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)) ↔
      IsPowerSeriesOver (fromClassical R) :=
  sorry

end CompleteLocalAlgCat
