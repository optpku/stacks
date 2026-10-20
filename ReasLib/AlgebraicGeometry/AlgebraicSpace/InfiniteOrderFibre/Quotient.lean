/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality

/-!
# Semilinear integer-translation quotient spaces

The small étale quotient sheaves of the spectrum and affine-line actions give algebraic
spaces over the integral base, with their canonical quotient projections and induced map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre

/-- The canonical projection from the field spectrum to its small étale quotient sheaf. -/
def atlasY (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    yoneda.obj (specOver K) ⟶ (specRelation K σ).smallEtaleQuotientSheaf.obj :=
  (specRelation K σ).smallEtaleQuotientSheafMk

/-- The quotient sheaf of an infinite-order spectrum action satisfies fppf descent. -/
theorem Y_isSheaf (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over base.{u})
      (specRelation K σ).smallEtaleQuotientSheaf.obj := sorry

/-- The quotient sheaf of an infinite-order spectrum action has representable diagonal. -/
theorem Y_representableDiagonal (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    yoneda.relativelyRepresentable
      (Limits.diag (specRelation K σ).smallEtaleQuotientSheaf.obj) := sorry

/-- The spectrum quotient projection for an infinite-order automorphism is representable
and étale. -/
theorem atlasY_etale (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale)) (atlasY K σ) := sorry

/-- The algebraic space obtained by quotienting the field spectrum by powers of an
infinite-order automorphism. -/
def Y (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    AlgebraicSpace base.{u} :=
  ofFunctor (specRelation K σ).smallEtaleQuotientSheaf.obj
    (Y_isSheaf K σ hσ) (Y_representableDiagonal K σ hσ)
    ⟨specOver K, atlasY K σ, atlasY_etale K σ hσ,
      PreRelation.instIsLocallySurjective_smallEtaleQuotientSheafMk (specRelation K σ)⟩

/-- The functor of points of the spectrum quotient is the small étale quotient sheaf. -/
theorem Y_functorOfPoints (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    (Y K σ hσ).functorOfPoints = (specRelation K σ).smallEtaleQuotientSheaf.obj := rfl

/-- The canonical projection from the affine line to its small étale quotient sheaf. -/
def atlasX (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    yoneda.obj (affineOver K) ⟶ (affineRelation K σ).smallEtaleQuotientSheaf.obj :=
  (affineRelation K σ).smallEtaleQuotientSheafMk

/-- The semilinear integer-translation quotient sheaf satisfies fppf descent. -/
theorem X_isSheaf (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over base.{u})
      (affineRelation K σ).smallEtaleQuotientSheaf.obj := sorry

/-- The semilinear integer-translation quotient sheaf has representable diagonal. -/
theorem X_representableDiagonal (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    yoneda.relativelyRepresentable
      (Limits.diag (affineRelation K σ).smallEtaleQuotientSheaf.obj) := sorry

/-- The semilinear integer-translation quotient projection is representable and étale. -/
theorem atlasX_etale (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale)) (atlasX K σ) := sorry

/-- The algebraic space obtained by quotienting the affine line by integer translation
together with the coefficient action of a field automorphism. -/
def X (K : Type u) [Field K] [CharZero K] (σ : RingAut K) : AlgebraicSpace base.{u} :=
  ofFunctor (affineRelation K σ).smallEtaleQuotientSheaf.obj
    (X_isSheaf K σ) (X_representableDiagonal K σ)
    ⟨affineOver K, atlasX K σ, atlasX_etale K σ,
      PreRelation.instIsLocallySurjective_smallEtaleQuotientSheafMk (affineRelation K σ)⟩

/-- The functor of points of the affine-line quotient is the small étale quotient sheaf. -/
theorem X_functorOfPoints (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    (X K σ).functorOfPoints = (affineRelation K σ).smallEtaleQuotientSheaf.obj := rfl

/-- The algebraic space represented by the field spectrum over the integral base. -/
def Z (K : Type u) [Field K] [CharZero K] : AlgebraicSpace base.{u} :=
  ofOver (specOver K)

/-- The functor of points of the represented field spectrum is its Yoneda presheaf. -/
theorem Z_functorOfPoints (K : Type u) [Field K] [CharZero K] :
    (Z K).functorOfPoints = yoneda.obj (specOver K) := rfl

/-- The algebraic space represented by the affine line over the integral base. -/
def W (K : Type u) [Field K] [CharZero K] : AlgebraicSpace base.{u} :=
  ofOver (affineOver K)

/-- The functor of points of the represented affine line is its Yoneda presheaf. -/
theorem W_functorOfPoints (K : Type u) [Field K] [CharZero K] :
    (W K).functorOfPoints = yoneda.obj (affineOver K) := rfl

/-- The quotient map from the affine line to its semilinear translation quotient. -/
def p (K : Type u) [Field K] [CharZero K] (σ : RingAut K) : W K ⟶ X K σ :=
  atlasX K σ

/-- The quotient map from the field spectrum to its infinite-order automorphism quotient. -/
def g (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    Z K ⟶ Y K σ hσ :=
  atlasY K σ

/-- The affine-line projection as a morphism of represented algebraic spaces. -/
def q (K : Type u) [Field K] [CharZero K] : W K ⟶ Z K :=
  ofOverMap (structureHom K)

/-- The map of quotient algebraic spaces induced by the equivariant affine-line projection. -/
def f (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    X K σ ⟶ Y K σ hσ :=
  (relationHom K σ).smallEtaleQuotientSheafMap

/-- The affine-line projection commutes with the two quotient projections. -/
theorem comm_sq (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    q K ≫ g K σ hσ = p K σ ≫ f K σ hσ := sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
