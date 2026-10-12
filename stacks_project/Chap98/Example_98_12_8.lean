/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.MvPolynomial.Solution
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField
public import ReasLib.RingTheory.Smooth.AtPrime.Lifting
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap98.Example_98_12_8_Coproduct
public import stacks_project.Chap98.Example_98_12_8_Functor
public import stacks_project.Chap98.Lemma_98_12_7_Approximate
import Mathlib.Tactic.CrossRefAttribute

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

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (m : MaximalSpectrum Λ)

/-- A maximal ideal `mA` of a `Λ`-algebra lies over `m` and identifies residue
fields `κ(m) = κ(mA)`. -/
def ResidueOverMaximal {A : Type u} [CommRing A] [Algebra Λ A]
    (mA : MaximalSpectrum A) : Prop :=
  PrimeSpectrum.comap (algebraMap Λ A) mA.toPrimeSpectrum = m.toPrimeSpectrum ∧
    RingHom.ResidueField.IsBijectiveAt (algebraMap Λ A) mA.toPrimeSpectrum

/-- `ResidueOverMaximal` unpacks the lying-over equality and the residue-field
bijection. -/
theorem ResidueOverMaximal_iff {A : Type u} [CommRing A] [Algebra Λ A]
    (mA : MaximalSpectrum A) :
    ResidueOverMaximal m mA ↔
      PrimeSpectrum.comap (algebraMap Λ A) mA.toPrimeSpectrum =
          m.toPrimeSpectrum ∧
        RingHom.ResidueField.IsBijectiveAt (algebraMap Λ A)
          mA.toPrimeSpectrum :=
  sorry

variable {C : Type u} [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]

/-- Example 98.12.8 (1): the structure morphism of the characteristic groupoid
of `U ⨿ Spec(C) ⟶ Spec(Λ)` is limit preserving on objects. -/
@[stacks 07XI, instance]
instance instLimitPreservingOnObjects :
    LimitPreservingOnObjects
      (baseProjection.{u + 1, u, u + 1} (groupoids m C)) :=
  sorry

variable (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum)

/-- Example 98.12.8 (2): the canonical formal object of the characteristic
groupoid over `Λ_m^∧` is effective. -/
@[stacks 07XI, instance]
instance instIsEffective_formalObject :
    FormalObject.IsEffective (formalObject m φ) :=
  sorry

/-- Example 98.12.8 (3): the canonical formal object of the characteristic
groupoid over `Λ_m^∧` is versal. -/
@[stacks 07XI]
theorem isVersalOnObjects_formalObject :
    FormalObject.IsVersalOnObjects (formalObject m φ) :=
  sorry

/-- Example 98.12.8 (4): if the characteristic groupoid admits an approximate
versal object, then there is a finite type `Λ`-algebra `A` and a maximal ideal
`m_A` lying over `m` with `κ(m) = κ(m_A)`, satisfying condition (4) of
Algebra, Lemma 10.141.2, together with a `Λ`-algebra map `C → A`. -/
@[stacks 07XI]
theorem exists_of_nonempty_approximateVersal
    (h : Nonempty (ApproximateVersal (formalObject m φ))) :
    ∃ (A : Type u) (instRing : CommRing A) (instAlg : Algebra Λ A)
      (instFT : Algebra.FiniteType Λ A) (mA : MaximalSpectrum A),
      @ResidueOverMaximal Λ _ m A instRing instAlg mA ∧
        @SmallExtensionLifts.withResidue Λ A
            _ instRing instAlg mA.toPrimeSpectrum ∧
          Nonempty (@AlgHom Λ C A _ _ instRing.toSemiring _ instAlg) :=
  sorry

/-- An approximate versal object yields a finite type `Λ`-algebra which is
smooth at a maximal ideal lying over `m`. -/
theorem isSmoothAt_of_nonempty_approximateVersal
    (h : Nonempty (ApproximateVersal (formalObject m φ))) :
    ∃ (A : Type u) (instRing : CommRing A) (instAlg : Algebra Λ A)
      (instFT : Algebra.FiniteType Λ A) (mA : MaximalSpectrum A),
      @ResidueOverMaximal Λ _ m A instRing instAlg mA ∧
        @Algebra.IsSmoothAt Λ A _ instRing instAlg mA.asIdeal mA.isMaximal.isPrime :=
  sorry

/-- After slicing, an approximate versal object yields a finite type
`Λ`-algebra which is étale at a maximal ideal lying over `m`. -/
theorem exists_etaleAt_slice
    (h : Nonempty (ApproximateVersal (formalObject m φ))) :
    ∃ (A : Type u) (instRing : CommRing A) (instAlg : Algebra Λ A)
      (instFT : Algebra.FiniteType Λ A) (mA : MaximalSpectrum A),
      @ResidueOverMaximal Λ _ m A instRing instAlg mA ∧
        @Algebra.IsEtaleAt Λ A _ instRing instAlg mA.asIdeal mA.isMaximal.isPrime :=
  sorry

/-- Example 98.12.8 (5): if every characteristic groupoid of a finite-type
factorization `Λ → C → Λ_m^∧` admits an approximate versal object, then
`Λ_m` is a G-ring. -/
@[stacks 07XI]
theorem isGRing_of_forall_nonempty_approximateVersal
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ))) :
    IsGRing (Localization.AtPrime m.asIdeal) :=
  sorry

/-- If every characteristic groupoid as above admits an approximate versal
object, then a finite polynomial system with a solution in `Λ_m^∧` has a
solution in any henselization of `Λ_m`, as a `Λ`-algebra via the tower
`Λ → Λ_m → Λ_m^h`. -/
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

/-- If every characteristic groupoid as above admits an approximate versal
object, then any henselization of `Λ_m` is a G-ring. -/
theorem isGRing_henselization_of_approximation
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ)))
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime m.asIdeal) Rh]
    [IsHenselizationOf (Localization.AtPrime m.asIdeal) Rh] :
    IsGRing Rh :=
  sorry

end AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity
