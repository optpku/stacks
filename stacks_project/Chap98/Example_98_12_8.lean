module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Factorization
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.GRingNecessity.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.GRingNecessity

/-! # Necessity of the G-ring hypothesis for approximating versal objects -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Factorization
open AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity
open AlgebraicGeometry.Groupoids.Hom
open CategoryTheory.FiberedCategoryOver.Groupoids
open PrimeSpectrum Algebra.IsSmoothAt

universe u

/- Example 98.12.8. Universal approximation of the characteristic formal objects
forces the local ring at the chosen maximal ideal to be a G-ring. -/
@[stacks 07XI] #check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.isGRing_of_forall_nonempty_approximateVersal :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ))),
    IsGRing (Localization.AtPrime m.asIdeal))

#check (AlgebraicGeometry.GroupoidsOver.Factorization.factorsThroughFunctor :
  ∀ {S S' : Scheme.{u}} (f : S' ⟶ S),
    (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.GroupoidsOver.Factorization.nonempty_factorsThroughFunctor_iff :
  ∀ {S S' : Scheme.{u}} (f : S' ⟶ S)
    (T : (Over S)ᵒᵖ),
    Nonempty ((factorsThroughFunctor f).obj T) ↔
      Nonempty (T.unop ⟶ Over.mk f))

#check (AlgebraicGeometry.GroupoidsOver.Factorization.toGroupoids :
  ∀ {S S' : Scheme.{u}} (f : S' ⟶ S),
    GroupoidsOver S)

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.coproduct :
  ∀ {Λ : Type u} [CommRing Λ] (m : MaximalSpectrum Λ) (C : Type u) [CommRing C],
    Scheme.{u})

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.coproductToS :
  ∀ {Λ : Type u} [CommRing Λ] (m : MaximalSpectrum Λ) (C : Type u) [CommRing C]
    [Algebra Λ C],
    coproduct m C ⟶ Spec (CommRingCat.of Λ))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.completeLocalSAlgebra_spec :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ),
    (completeLocalSAlgebra m).carrier =
      CompletedLocalRing m.toPrimeSpectrum ∧
      (completeLocalSAlgebra m).toS =
        Spec.map (CommRingCat.ofHom
          (algebraMap Λ (CompletedLocalRing m.toPrimeSpectrum))))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.formalObject :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {C : Type u} [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C] (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
    FormalObject (groupoids m C))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.formalObject_spec :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {C : Type u} [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C] (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ),
    (groupoids m C).p.obj ((formalObject m φ).objects n) =
        (formalObject m φ).base.stageOver n ∧
      (groupoids m C).p.IsHomLift ((formalObject m φ).base.stageHom n)
        ((formalObject m φ).step n))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.instLimitPreservingOnObjects :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {C : Type u} [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C],
    LimitPreservingOnObjects
      (baseProjection.{u + 1, u, u + 1} (groupoids m C)))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.instIsEffective_formalObject :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {C : Type u} [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) [Algebra.FiniteType Λ C],
    FormalObject.IsEffective (formalObject m φ))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.isVersalOnObjects_formalObject :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {C : Type u} [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) [Algebra.FiniteType Λ C],
    FormalObject.IsVersalOnObjects (formalObject m φ))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.exists_of_nonempty_approximateVersal :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {C : Type u} [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) [Algebra.FiniteType Λ C]
    (h : Nonempty (ApproximateVersal (formalObject m φ))),
    ∃ A : CommAlgCat.{u} Λ, Algebra.FiniteType Λ A ∧
      ∃ mA : MaximalSpectrum A,
        ResidueOverMaximal m mA ∧
          SmallExtensionLifts.withResidue.{u, u, u, u}
            (R := Λ) (S := A) mA.toPrimeSpectrum ∧
            Nonempty (C →ₐ[Λ] A))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.isSmoothAt_of_nonempty_approximateVersal :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {C : Type u} [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) [Algebra.FiniteType Λ C]
    (h : Nonempty (ApproximateVersal (formalObject m φ))),
    ∃ A : CommAlgCat.{u} Λ, Algebra.FiniteType Λ A ∧
      ∃ mA : MaximalSpectrum A,
        ResidueOverMaximal m mA ∧
          Algebra.IsSmoothAt Λ mA.asIdeal ∧ Nonempty (C →ₐ[Λ] A))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.exists_etaleAt_slice :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {C : Type u} [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) [Algebra.FiniteType Λ C]
    (h : Nonempty (ApproximateVersal (formalObject m φ))),
    ∃ A : CommAlgCat.{u} Λ, Algebra.FiniteType Λ A ∧
      ∃ mA : MaximalSpectrum A,
        ResidueOverMaximal m mA ∧
          Algebra.IsEtaleAt Λ mA.asIdeal ∧ Nonempty (C →ₐ[Λ] A))

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.exists_solution_in_henselization :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) {σ ι : Type u} [Finite σ] [Finite ι] (f : ι → MvPolynomial σ Λ)
    (aHat : σ → CompletedLocalRing m.toPrimeSpectrum)
    (hf : MvPolynomial.IsSolution f aHat)
    (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ)))
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime m.asIdeal) Rh]
    [Algebra Λ Rh]
    [IsScalarTower Λ (Localization.AtPrime m.asIdeal) Rh]
    [IsHenselizationOf (Localization.AtPrime m.asIdeal) Rh],
    ∃ a : σ → Rh, MvPolynomial.IsSolution f a)

#check (AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity.isGRing_henselization_of_approximation :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : MaximalSpectrum Λ) (h : ∀ (C : Type u) [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]
      (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum),
      Nonempty (ApproximateVersal (formalObject m φ)))
    (Rh : Type u) [CommRing Rh] [Algebra (Localization.AtPrime m.asIdeal) Rh]
    [IsHenselizationOf (Localization.AtPrime m.asIdeal) Rh],
    IsGRing Rh)
