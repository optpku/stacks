/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_54_5
public import stacks_project.Chap42.Lemma_42_55_3
public import ReasLib.AlgebraicGeometry.LocalizedChern.Fundamental
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.55.4 (1): the localized Chern caps vanish for `0 < t < r`. -/
@[stacks 0FEH] #check (AlgebraicGeometry.LocalizedChern.chernClass_pushforwardStructureSheaf_cap_fundamental_eq_zero :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
    (t : ℕ) (ht : 0 < t) (htr : t < r),
    let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
    let setup : Situation S δ X i E t .rankBound :=
      pushforwardStructureSheafSituation δ X.hom i hX t ht
    capOnFundamental X i
      (chernClass i classes E setup.perfect t setup.offCenter setup.finiteness) n = 0)

/- Lemma 42.55.4 (2): the top localized Chern cap is the signed factorial multiple of `[Z]`. -/
@[stacks 0FEH] #check (AlgebraicGeometry.LocalizedChern.chernClass_pushforwardStructureSheaf_cap_fundamental :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
    (hr : 0 < r),
    let E := (Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj
    let setup : Situation S δ X i E r .rankBound :=
      pushforwardStructureSheafSituation δ X.hom i hX r hr
    capOnFundamental X i
      (chernClass i classes E setup.perfect r setup.offCenter setup.finiteness) n =
      (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ)) •
        RelativeChow.fundamentalClass δ (Over.mk (i ≫ X.hom)) (n - (r : ℤ)))

/- Lemma 42.55.4 (3): the localized Chern-character caps vanish for `t < r`, including zero. -/
@[stacks 0FEH] #check (AlgebraicGeometry.LocalizedChern.character_pushforwardStructureSheaf_cap_fundamental_eq_zero :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
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
    (t : ℕ) (htr : t < r),
    characterCapOnFundamental i classes
      (Scheme.DerivedQCoh.pushforwardStructureSheaf_isPerfect i
        (IsRegularImmersion.isPerfect i))
      (pushforwardStructureSheaf_restrictAway_isZero i)
      (hX.elim TechnicalCondition.quasiCompact TechnicalCondition.quasiCompactComponents) t n = 0)

/- Lemma 42.55.4 (4): the top localized Chern-character cap equals the rational class `[Z]`. -/
@[stacks 0FEH] #check (AlgebraicGeometry.LocalizedChern.character_pushforwardStructureSheaf_cap_fundamental :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory δ X.hom)
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (n : ℤ)
    (hdim : (⨆ η : genericPoints X.left,
      (X.hom.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt)),
    characterCapOnFundamental i classes
      (Scheme.DerivedQCoh.pushforwardStructureSheaf_isPerfect i
        (IsRegularImmersion.isPerfect i))
      (pushforwardStructureSheaf_restrictAway_isZero i)
      (hX.elim TechnicalCondition.quasiCompact TechnicalCondition.quasiCompactComponents) r n =
      TensorProduct.tmul ℤ (RelativeChow.fundamentalClass δ (Over.mk (i ≫ X.hom)) (n - (r : ℤ))) (1 : ℚ))

end AlgebraicGeometry.LocalizedChern
