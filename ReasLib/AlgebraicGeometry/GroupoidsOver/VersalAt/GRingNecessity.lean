/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.MvPolynomial.Solution
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField
public import ReasLib.RingTheory.Smooth.AtPrime.Lifting
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.Approximation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.GRingNecessity.Basic

/-!
# Necessity of the G-ring hypothesis for approximating versal objects

For a Noetherian ring `Λ` and a maximal ideal `m`, characteristic groupoids of
factorizations through `U ⨿ Spec(C)` are limit preserving on objects and carry
an effective versal formal object over `Λ_m^∧`. If every such groupoid admits
an approximate versal object, then `Λ_m` is a G-ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity
open CategoryTheory.FiberedCategoryOver.Groupoids
open PrimeSpectrum
open Algebra.IsSmoothAt

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity

variable {Λ : Type u} [CommRing Λ] [noetherian : IsNoetherianRing Λ]
variable (m : MaximalSpectrum Λ)

/-- A maximal ideal `mA` of a `Λ`-algebra lies over `m` and identifies residue fields `κ(m) =
κ(mA)`. -/
def ResidueOverMaximal {A : Type u} [CommRing A] [Algebra Λ A]
    (mA : MaximalSpectrum A) : Prop :=
  PrimeSpectrum.comap (algebraMap Λ A) mA.toPrimeSpectrum = m.toPrimeSpectrum ∧
    RingHom.ResidueField.IsBijectiveAt (algebraMap Λ A) mA.toPrimeSpectrum

/-- `ResidueOverMaximal` unpacks the lying-over equality and the residue-field bijection. -/
theorem ResidueOverMaximal_iff {A : Type u} [CommRing A] [Algebra Λ A]
    (mA : MaximalSpectrum A) :
    ResidueOverMaximal m mA ↔
      PrimeSpectrum.comap (algebraMap Λ A) mA.toPrimeSpectrum =
          m.toPrimeSpectrum ∧
        RingHom.ResidueField.IsBijectiveAt (algebraMap Λ A)
          mA.toPrimeSpectrum :=
  sorry

variable {C : Type u} [CommRing C] [Algebra Λ C]

include noetherian in
/-- The characteristic groupoid of the punctured-spectrum coproduct with a finite-type algebra is
limit preserving on objects. -/
instance instLimitPreservingOnObjects [Algebra.FiniteType Λ C] :
    LimitPreservingOnObjects
      (baseProjection.{u + 1, u, u + 1} (groupoids m C)) :=
  sorry

variable (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum)

/-- The formal object obtained from a factorization through a finite-type algebra into the completed
local ring is effective. -/
instance instIsEffective_formalObject [Algebra.FiniteType Λ C] :
    FormalObject.IsEffective (formalObject m φ) :=
  sorry

/-- The formal object obtained from a factorization through a finite-type algebra into the completed
local ring is versal on objects. -/
theorem isVersalOnObjects_formalObject [Algebra.FiniteType Λ C] :
    FormalObject.IsVersalOnObjects (formalObject m φ) :=
  sorry

/-- An approximation of the characteristic formal object yields a finite-type algebra receiving the
given algebra, with a maximal point over the chosen point, a bijective residue map, and the
residue-compatible small-extension lifting property. -/
theorem exists_of_nonempty_approximateVersal [Algebra.FiniteType Λ C]
    (h : Nonempty (ApproximateVersal (formalObject m φ))) :
    ∃ A : CommAlgCat.{u} Λ, Algebra.FiniteType Λ A ∧
      ∃ mA : MaximalSpectrum A,
        ResidueOverMaximal m mA ∧
          SmallExtensionLifts.withResidue.{u, u, u, u}
            (R := Λ) (S := A) mA.toPrimeSpectrum ∧
            Nonempty (C →ₐ[Λ] A) :=
  sorry

/-- An approximation of the characteristic formal object yields a finite-type algebra receiving the
given algebra and smooth at a maximal point over the chosen point with the same residue field. -/
theorem isSmoothAt_of_nonempty_approximateVersal [Algebra.FiniteType Λ C]
    (h : Nonempty (ApproximateVersal (formalObject m φ))) :
    ∃ A : CommAlgCat.{u} Λ, Algebra.FiniteType Λ A ∧
      ∃ mA : MaximalSpectrum A,
        ResidueOverMaximal m mA ∧
          Algebra.IsSmoothAt Λ mA.asIdeal ∧ Nonempty (C →ₐ[Λ] A) :=
  sorry

/-- An approximation of the characteristic formal object yields a finite-type algebra receiving the
given algebra and étale at a maximal point over the chosen point with the same residue field. -/
theorem exists_etaleAt_slice [Algebra.FiniteType Λ C]
    (h : Nonempty (ApproximateVersal (formalObject m φ))) :
    ∃ A : CommAlgCat.{u} Λ, Algebra.FiniteType Λ A ∧
      ∃ mA : MaximalSpectrum A,
        ResidueOverMaximal m mA ∧
          Algebra.IsEtaleAt Λ mA.asIdeal ∧ Nonempty (C →ₐ[Λ] A) :=
  sorry

/-- If the characteristic groupoid of every finite-type factorization into the completed local ring
admits an approximate versal object, then a finite polynomial system with a solution in `Λ_m^∧`
has a solution in any henselization of `Λ_m`, as a `Λ`-algebra via the tower `Λ → Λ_m → Λ_m^h`. -/
theorem exists_solution_in_henselization
    {σ ι : Type u} [Finite σ] [Finite ι] (f : ι → MvPolynomial σ Λ)
    (aHat : σ → CompletedLocalRing m.toPrimeSpectrum)
    (hf : MvPolynomial.IsSolution f aHat)
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ)))
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime m.asIdeal) Rh]
    [Algebra Λ Rh]
    [IsScalarTower Λ (Localization.AtPrime m.asIdeal) Rh]
    [IsHenselizationOf (Localization.AtPrime m.asIdeal) Rh] :
    ∃ a : σ → Rh, MvPolynomial.IsSolution f a :=
  sorry

/-- If the characteristic groupoid of every finite-type factorization into the completed local ring
admits an approximate versal object, then any henselization of `Λ_m` is a G-ring. -/
theorem isGRing_henselization_of_approximation
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ)))
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime m.asIdeal) Rh]
    [IsHenselizationOf (Localization.AtPrime m.asIdeal) Rh] :
    IsGRing Rh :=
  sorry

/-- If every finite-type factorization into the completed local ring admits an approximate versal
object for its characteristic groupoid, then the local ring at the chosen maximal ideal is a
G-ring. -/
theorem isGRing_of_forall_nonempty_approximateVersal
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ))) :
    IsGRing (Localization.AtPrime m.asIdeal) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity
