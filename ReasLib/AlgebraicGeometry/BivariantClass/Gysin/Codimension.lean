/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Descent
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom.VirtualNormalBundle

/-- Flat restriction to an open of the dimension-`n` stratum, in codimension `a`. -/
def restrictInCodimension {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X W : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType W.hom]
    (D : X.hom.GenericDimensionStratification δ) (n : ℤ)
    (j : W ⟶ ComponentRestriction.over X (D.stratum n)) [IsOpenImmersion j.left]
    (a : ℤ) : ChowGroup.Codimension D a →+ RelativeChow δ W (n - a) :=
  (RelativeChow.castDegree δ (add_zero (n - a))).comp
    ((@ChowGroup.flatPullback S inferInstance δ inferInstance W
      (ComponentRestriction.over X (D.stratum n)) inferInstance inferInstance j 0
      inferInstance (Scheme.Hom.relativeDimension_zero_of_isOpenImmersion j.left)
      (n - a)).comp (Pi.evalAddMonoidHom _ n))

/-- Rational flat restriction is obtained by tensoring the integral restriction with `ℚ`. -/
def restrictInCodimensionQ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X W : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType W.hom]
    (D : X.hom.GenericDimensionStratification δ) (n : ℤ)
    (j : W ⟶ ComponentRestriction.over X (D.stratum n)) [IsOpenImmersion j.left]
    (a : ℤ) : TensorProduct ℤ (ChowGroup.Codimension D a) ℚ →ₗ[ℤ]
      TensorProduct ℤ (RelativeChow δ W (n - a)) ℚ :=
  TensorProduct.map (restrictInCodimension δ D n j a).toIntLinearMap LinearMap.id



/-- Integral Gysin descent in codimension `a` tests every local geometric presentation;
all coefficients other than the dimension difference vanish. -/
def IsImageInCodimension {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (a : ℤ) (α : ChowGroup.Codimension DY a) (β : ChowGroup.Codimension DX a) : Prop :=
  ∀ (A B C E P : Over S)
    [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
    [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType P.hom]
    (jA : A ⟶ X) [IsOpenImmersion jA.left]
    (jB : B ⟶ Y) [IsOpenImmersion jB.left]
    (n m : ℤ)
    (jC : C ⟶ ComponentRestriction.over X' (DX.stratum n))
    [IsOpenImmersion jC.left]
    (jE : E ⟶ ComponentRestriction.over Y' (DY.stratum m))
    [IsOpenImmersion jE.left]
    (f₀ : A ⟶ B) (i₀ : C ⟶ A) (f₀' : C ⟶ E) (g₀ : E ⟶ B)
    [LocallyOfFiniteType g₀.left],
    f₀ ≫ jB = jA ≫ f →
    i₀ ≫ jA = jC ≫ ComponentRestriction.ι X' (DX.stratum n) ≫ i →
    f₀' ≫ jE ≫ ComponentRestriction.ι Y' (DY.stratum m) =
      jC ≫ ComponentRestriction.ι X' (DX.stratum n) ≫ f' →
    g₀ ≫ jB = jE ≫ ComponentRestriction.ι Y' (DY.stratum m) ≫ g →
    ∀ (square₀ : IsPullback i₀.left f₀'.left f₀.left g₀.left)
      (ι : A ⟶ P) (σ : P ⟶ B) [IsRegularImmersion ι.left] [Smooth σ.left]
      (hfac : ι ≫ σ = f₀)
      (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
        Scheme.Hom.conormalSheaf ι.left)
      (D : ClosedDeformation A.hom (ι.left.coborderRange.ι ≫ P.hom)
        ι.left.liftCoborder
        ((Category.assoc ι.left.liftCoborder ι.left.coborderRange.ι P.hom).symm.trans
          ((congrArg (fun k ↦ k ≫ P.hom) ι.left.liftCoborder_ι).trans (Over.w ι)))
        (normalBundle ι.left e).toCoborder)
      (p : ℤ),
      if p = m - n then
        HEq ((factorizationClassDegree δ f₀ ι σ hfac e D p).cap i₀ f₀' g₀ square₀ (m - a)
          (restrictInCodimension δ DY m jE a α)) (restrictInCodimension δ DX n jC a β)
      else
        (factorizationClassDegree δ f₀ ι σ hfac e D p).cap i₀ f₀' g₀ square₀ (m - a)
          (restrictInCodimension δ DY m jE a α) = 0


/-- Rational Gysin descent requires global integral representatives with one positive
common denominator satisfying integral descent, together with all rational local
presentation tests, including every off-degree vanishing condition. -/
def IsImageInCodimensionQ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (a : ℤ) (α : TensorProduct ℤ (ChowGroup.Codimension DY a) ℚ)
    (β : TensorProduct ℤ (ChowGroup.Codimension DX a) ℚ) : Prop :=
  (∃ (N : ℕ) (α₀ : ChowGroup.Codimension DY a) (β₀ : ChowGroup.Codimension DX a),
    0 < N ∧
      α = TensorProduct.tmul ℤ α₀ ((N : ℚ)⁻¹) ∧
      β = TensorProduct.tmul ℤ β₀ ((N : ℚ)⁻¹) ∧
      IsImageInCodimension δ f i f' g DX DY a α₀ β₀) ∧
  ∀ (A B C E P : Over S)
    [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
    [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType P.hom]
    (jA : A ⟶ X) [IsOpenImmersion jA.left]
    (jB : B ⟶ Y) [IsOpenImmersion jB.left]
    (n m : ℤ)
    (jC : C ⟶ ComponentRestriction.over X' (DX.stratum n))
    [IsOpenImmersion jC.left]
    (jE : E ⟶ ComponentRestriction.over Y' (DY.stratum m))
    [IsOpenImmersion jE.left]
    (f₀ : A ⟶ B) (i₀ : C ⟶ A) (f₀' : C ⟶ E) (g₀ : E ⟶ B)
    [LocallyOfFiniteType g₀.left],
    f₀ ≫ jB = jA ≫ f →
    i₀ ≫ jA = jC ≫ ComponentRestriction.ι X' (DX.stratum n) ≫ i →
    f₀' ≫ jE ≫ ComponentRestriction.ι Y' (DY.stratum m) =
      jC ≫ ComponentRestriction.ι X' (DX.stratum n) ≫ f' →
    g₀ ≫ jB = jE ≫ ComponentRestriction.ι Y' (DY.stratum m) ≫ g →
    ∀ (square₀ : IsPullback i₀.left f₀'.left f₀.left g₀.left)
      (ι : A ⟶ P) (σ : P ⟶ B) [IsRegularImmersion ι.left] [Smooth σ.left]
      (hfac : ι ≫ σ = f₀)
      (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
        Scheme.Hom.conormalSheaf ι.left)
      (D : ClosedDeformation A.hom (ι.left.coborderRange.ι ≫ P.hom)
        ι.left.liftCoborder
        ((Category.assoc ι.left.liftCoborder ι.left.coborderRange.ι P.hom).symm.trans
          ((congrArg (fun k ↦ k ≫ P.hom) ι.left.liftCoborder_ι).trans (Over.w ι)))
        (normalBundle ι.left e).toCoborder)
      (p : ℤ),
      if p = m - n then
        HEq (TensorProduct.map
          ((factorizationClassDegree δ f₀ ι σ hfac e D p).cap
            i₀ f₀' g₀ square₀ (m - a)).toIntLinearMap LinearMap.id
          (restrictInCodimensionQ δ DY m jE a α)) (restrictInCodimensionQ δ DX n jC a β)
      else
        TensorProduct.map
          ((factorizationClassDegree δ f₀ ι σ hfac e D p).cap
            i₀ f₀' g₀ square₀ (m - a)).toIntLinearMap LinearMap.id
          (restrictInCodimensionQ δ DY m jE a α) = 0


/-- The partial integral Gysin action selects the unique class satisfying geometric descent
only when a unique such class exists. -/
def capInCodimension {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (a : ℤ) (α : ChowGroup.Codimension DY a) : Part (ChowGroup.Codimension DX a) where
  Dom := ∃! β, IsImageInCodimension δ f i f' g DX DY a α β
  get h := Classical.choose h


/-- The partial rational Gysin action selects the unique class admitting a global
common-denominator integral descent witness and satisfying the rational local tests,
only when a unique such class exists. -/
def capInCodimensionQ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (a : ℤ) (α : TensorProduct ℤ (ChowGroup.Codimension DY a) ℚ) :
    Part (TensorProduct ℤ (ChowGroup.Codimension DX a) ℚ) where
  Dom := ∃! β, IsImageInCodimensionQ δ f i f' g DX DY a α β
  get h := Classical.choose h


/-- A defined integral Gysin image is characterized by geometric descent and uniqueness. -/
theorem capInCodimension_eq_some_iff {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (a : ℤ) (α : ChowGroup.Codimension DY a) (β : ChowGroup.Codimension DX a) :
    capInCodimension δ f i f' g DX DY a α = Part.some β ↔
      IsImageInCodimension δ f i f' g DX DY a α β ∧
        ∀ γ, IsImageInCodimension δ f i f' g DX DY a α γ → γ = β := sorry

/-- A defined rational Gysin image is characterized by global common-denominator integral
descent, the rational local tests, and uniqueness. -/
theorem capInCodimensionQ_eq_some_iff {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (a : ℤ) (α : TensorProduct ℤ (ChowGroup.Codimension DY a) ℚ)
    (β : TensorProduct ℤ (ChowGroup.Codimension DX a) ℚ) :
    capInCodimensionQ δ f i f' g DX DY a α = Part.some β ↔
      IsImageInCodimensionQ δ f i f' g DX DY a α β ∧
        ∀ γ, IsImageInCodimensionQ δ f i f' g DX DY a α γ → γ = β := sorry

/-- In codimension zero the integral action agrees with the original full Gysin action. -/
theorem capInCodimension_zero {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (DX : X'.hom.GenericDimensionStratification δ)
    (DY : Y'.hom.GenericDimensionStratification δ)
    (α : ChowGroup.Codimension DY 0) :
    capInCodimension δ f i f' g DX DY 0 α = cap δ f i f' g DX DY α := sorry


end AlgebraicGeometry.BivariantClass.Gysin
