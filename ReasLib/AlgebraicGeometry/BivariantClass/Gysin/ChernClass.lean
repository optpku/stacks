/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Codimension.Cap
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter.Cap
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Codimension
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Commutation
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Fundamental
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The integer-degree Gysin coefficients of a local complete intersection morphism
commute with the canonical Chern classes and their pullbacks, for every immersion–smooth
presentation, with regularity and deformation realizations asserted in the conclusion. -/
theorem gysin_commute_chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (hf : HasGysinMap f)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    ∀ (P : Over S) [LocallyOfFiniteType P.hom]
      (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
      [hσ : Smooth σ.left] (hfac : ι ≫ σ = f),
    ∃ hreg : IsRegularImmersion ι.left,
    ∃ e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left,
    ∃ D : ClosedDeformation X.hom (ι.left.coborderRange.ι ≫ P.hom)
      ι.left.liftCoborder
      ((Category.assoc ι.left.liftCoborder ι.left.coborderRange.ι P.hom).symm.trans
        ((congrArg (fun k ↦ k ≫ P.hom) ι.left.liftCoborder_ι).trans (Over.w ι)))
      (@Gysin.normalBundle X.left P.left ι.left hreg e).toCoborder,
    ∀ (p k : ℤ),
      let G := @Gysin.factorizationClassDegree S inferInstance δ inferInstance X Y P
        inferInstance inferInstance inferInstance f ι σ hreg hσ hfac e D p
      HEq
        ((G.cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst (k - (i : ℤ))).comp
          ((ChernClass.chernClass δ Y.hom E i).cap
            (𝟙 Y) (𝟙 Y) (𝟙 Y) IsPullback.of_id_snd k))
        (((ChernClass.chernClass δ X.hom ((Scheme.Modules.pullback f.left).obj E) i).cap
          (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd (k - p)).comp
          (G.cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst k)) := sorry

/-- The integer-degree Gysin coefficients of a local complete intersection morphism
commute with every rational Chern-character component, computed as Newton cap divided by
`i!`, for every immersion–smooth presentation. -/
theorem gysin_commute_character
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (hf : HasGysinMap f)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    ∀ (P : Over S) [LocallyOfFiniteType P.hom]
      (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
      [hσ : Smooth σ.left] (hfac : ι ≫ σ = f),
    ∃ hreg : IsRegularImmersion ι.left,
    ∃ e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left,
    ∃ D : ClosedDeformation X.hom (ι.left.coborderRange.ι ≫ P.hom)
      ι.left.liftCoborder
      ((Category.assoc ι.left.liftCoborder ι.left.coborderRange.ι P.hom).symm.trans
        ((congrArg (fun k ↦ k ≫ P.hom) ι.left.liftCoborder_ι).trans (Over.w ι)))
      (@Gysin.normalBundle X.left P.left ι.left hreg e).toCoborder,
    ∀ (p k : ℤ),
      let G := @Gysin.factorizationClassDegree S inferInstance δ inferInstance X Y P
        inferInstance inferInstance inferInstance f ι σ hreg hσ hfac e D p
      HEq
        ((TensorProduct.map
          (G.cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst (k - (i : ℤ))).toIntLinearMap
          (LinearMap.id : ℚ →ₗ[ℤ] ℚ)).comp
          (ChernClass.Theory.characterCap δ (ChernClass.Theory.canonical δ Y.hom) E i k))
        ((ChernClass.Theory.characterCap δ (ChernClass.Theory.canonical δ X.hom)
          ((Scheme.Modules.pullback f.left).obj E) i (k - p)).comp
          (TensorProduct.map
            (G.cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst k).toIntLinearMap
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ))) := sorry

/-- For a local complete intersection morphism admitting a Gysin map between locally
equidimensional schemes, with Cohen–Macaulay target, Gysin pullback sends the full
fundamental class of the target to that of the source. -/
theorem gysin_cap_fundamentalClass_id
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (hf : HasGysinMap f)
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    [Scheme.CohenMacaulay Y.left] :
    let DX := GenericDimensionStratification.ofPointwise X.hom δ hX
    let DY := GenericDimensionStratification.ofPointwise Y.hom δ hY
    Gysin.cap δ f (𝟙 X) f (𝟙 Y) DX DY
        (ChowGroup.Codimension.fundamentalClass DY) =
      Part.some (ChowGroup.Codimension.fundamentalClass DX) := sorry

/-- For a local complete intersection morphism admitting a Gysin map between locally
equidimensional schemes, with Cohen–Macaulay target, Gysin pullback preserves intersections
of canonical Chern classes with the full fundamental class. -/
theorem gysin_cap_chernClass_fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (hf : HasGysinMap f)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ)
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    [Scheme.CohenMacaulay Y.left] :
    let DX := GenericDimensionStratification.ofPointwise X.hom δ hX
    let DY := GenericDimensionStratification.ofPointwise Y.hom δ hY
    Gysin.capInCodimension δ f (𝟙 X) f (𝟙 Y) DX DY (i : ℤ)
        (zero_add (i : ℤ) ▸
          ChowGroup.Codimension.cap δ DY 0 (i : ℤ) (ChernClass.chernClass δ Y.hom E i)
            (ChowGroup.Codimension.fundamentalClass DY)) =
      Part.some (zero_add (i : ℤ) ▸
        ChowGroup.Codimension.cap δ DX 0 (i : ℤ)
          (ChernClass.chernClass δ X.hom ((Scheme.Modules.pullback f.left).obj E) i)
          (ChowGroup.Codimension.fundamentalClass DX)) := sorry

/-- For a local complete intersection morphism admitting a Gysin map between locally
equidimensional schemes, with Cohen–Macaulay target, rational Gysin pullback preserves
intersections of every Chern-character component with the full fundamental class. -/
theorem gysin_cap_character_fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (hf : HasGysinMap f)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ)
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    [Scheme.CohenMacaulay Y.left] :
    let DX := GenericDimensionStratification.ofPointwise X.hom δ hX
    let DY := GenericDimensionStratification.ofPointwise Y.hom δ hY
    Gysin.capInCodimensionQ δ f (𝟙 X) f (𝟙 Y) DX DY (i : ℤ)
        (zero_add (i : ℤ) ▸
          ChowGroup.Codimension.characterCap δ DY 0 (ChernClass.Theory.canonical δ Y.hom)
            E i (TensorProduct.tmul ℤ (ChowGroup.Codimension.fundamentalClass DY) 1)) =
      Part.some (zero_add (i : ℤ) ▸
        ChowGroup.Codimension.characterCap δ DX 0 (ChernClass.Theory.canonical δ X.hom)
          ((Scheme.Modules.pullback f.left).obj E) i
          (TensorProduct.tmul ℤ (ChowGroup.Codimension.fundamentalClass DX) 1)) := sorry

end AlgebraicGeometry.BivariantClass
