/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.RegularImmersion
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- Identity-horizontal evaluation of a bivariant class on the degree-`n` fundamental
class of `X`. -/
noncomputable def capOnFundamental
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ X.hom)]
    {d : ℤ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) d)
    (n : ℤ) :
    RelativeChow δ (Over.mk (i ≫ X.hom)) (n - d) :=
  c.cap (𝟙 (Over.mk (i ≫ X.hom))) (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (𝟙 X)
    (IsPullback.id_horiz i) n (RelativeChow.fundamentalClass δ X n)

/-- `capOnFundamental` is the identity-horizontal cap against `[X]_n`. -/
theorem capOnFundamental_def
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ X.hom)]
    {d : ℤ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) d)
    (n : ℤ) :
    capOnFundamental X i c n =
      c.cap (𝟙 (Over.mk (i ≫ X.hom))) (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (𝟙 X)
        (IsPullback.id_horiz i) n (RelativeChow.fundamentalClass δ X n) := rfl

/-- The derived module `i_* 𝒪_Z` vanishes on the open complement of a closed immersion. -/
theorem pushforwardStructureSheaf_restrictAway_isZero
    {Z X : Scheme.{u}} (i : Z ⟶ X) [hclosed : IsClosedImmersion i] :
    IsZero (restrictAway i
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj) :=
  sorry

/-- The identity-horizontal cap of the degree-`t` localized Chern character of `i_* 𝒪_Z`
against `[X]_n`, realized as the Newton-class cap tensored with `(t!)⁻¹`. -/
noncomputable def characterCapOnFundamental
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [hclosed : IsClosedImmersion i] [LocallyOfFiniteType (i ≫ X.hom)]
    (classes : ChernClass.Theory δ X.hom)
    (perfect : RingedSpace.ModuleDerived.IsPerfect
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj)
    (vanishing : IsZero (restrictAway i
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj))
    (finiteness : TechnicalCondition X
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj)
    (t : ℕ) (n : ℤ) :
    TensorProduct ℤ (RelativeChow δ (Over.mk (i ≫ X.hom)) (n - (t : ℤ))) ℚ :=
  let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
  TensorProduct.tmul ℤ
    (capOnFundamental X i (newtonClass i classes E perfect vanishing finiteness t) n)
    ((t.factorial : ℚ)⁻¹)

/-- `characterCapOnFundamental` is the Newton-class cap of `i_* 𝒪_Z` scaled by `(t!)⁻¹`. -/
theorem characterCapOnFundamental_def
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [hclosed : IsClosedImmersion i] [LocallyOfFiniteType (i ≫ X.hom)]
    (classes : ChernClass.Theory δ X.hom)
    (perfect : RingedSpace.ModuleDerived.IsPerfect
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj)
    (vanishing : IsZero (restrictAway i
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj))
    (finiteness : TechnicalCondition X
      (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj)
    (t : ℕ) (n : ℤ) :
    characterCapOnFundamental i classes perfect vanishing finiteness t n =
      let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
      TensorProduct.tmul ℤ
        (capOnFundamental X i (newtonClass i classes E perfect vanishing finiteness t) n)
        ((t.factorial : ℚ)⁻¹) := rfl

/-- The positive-degree localized Chern caps of the pushed-forward structure sheaf of a
regular closed immersion vanish below its constant codimension. -/
theorem chernClass_pushforwardStructureSheaf_cap_fundamental_eq_zero
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory δ X.hom)
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (n : ℤ)
    (hdim : (⨆ η : genericPoints X.left,
      (X.hom.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt))
    (t : ℕ) (ht : 0 < t) (htr : t < r) :
    let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
    let setup : Situation S δ X i E t .rankBound :=
      pushforwardStructureSheafSituation δ X.hom i hX t ht
    capOnFundamental X i
      (chernClass i classes E setup.perfect t setup.offCenter setup.finiteness) n = 0 := sorry

/-- The top localized Chern cap of the pushed-forward structure sheaf of a positive
codimension regular closed immersion is the signed factorial multiple of its fundamental class. -/
theorem chernClass_pushforwardStructureSheaf_cap_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory δ X.hom)
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (n : ℤ)
    (hdim : (⨆ η : genericPoints X.left,
      (X.hom.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt))
    (hr : 0 < r) :
    let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
    let setup : Situation S δ X i E r .rankBound :=
      pushforwardStructureSheafSituation δ X.hom i hX r hr
    capOnFundamental X i
      (chernClass i classes E setup.perfect r setup.offCenter setup.finiteness) n =
      (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ)) •
        RelativeChow.fundamentalClass δ (Over.mk (i ≫ X.hom)) (n - (r : ℤ)) := sorry

/-- The localized Chern-character caps of the pushed-forward structure sheaf of a
regular closed immersion vanish in every nonnegative degree below its constant codimension. -/
theorem character_pushforwardStructureSheaf_cap_fundamental_eq_zero
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory δ X.hom)
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (n : ℤ)
    (hdim : (⨆ η : genericPoints X.left,
      (X.hom.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt))
    (t : ℕ) (htr : t < r) :
    characterCapOnFundamental i classes
      (Scheme.DerivedQCoh.pushforwardStructureSheaf_isPerfect i
        (IsRegularImmersion.isPerfect i))
      (pushforwardStructureSheaf_restrictAway_isZero i)
      (hX.elim TechnicalCondition.quasiCompact TechnicalCondition.quasiCompactComponents) t n = 0 := sorry

/-- The top localized Chern-character cap of the pushed-forward structure sheaf of a
regular closed immersion is its rational fundamental class, including in codimension zero. -/
theorem character_pushforwardStructureSheaf_cap_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory δ X.hom)
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (n : ℤ)
    (hdim : (⨆ η : genericPoints X.left,
      (X.hom.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt)) :
    characterCapOnFundamental i classes
      (Scheme.DerivedQCoh.pushforwardStructureSheaf_isPerfect i
        (IsRegularImmersion.isPerfect i))
      (pushforwardStructureSheaf_restrictAway_isZero i)
      (hX.elim TechnicalCondition.quasiCompact TechnicalCondition.quasiCompactComponents) r n =
      TensorProduct.tmul ℤ (RelativeChow.fundamentalClass δ (Over.mk (i ≫ X.hom)) (n - (r : ℤ))) (1 : ℚ) :=
  sorry

end AlgebraicGeometry.LocalizedChern
