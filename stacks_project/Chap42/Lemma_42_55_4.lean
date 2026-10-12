/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_54_5
public import stacks_project.Chap42.Lemma_42_55_3

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
    (IsPullback.id_horiz i) n (fundamentalClass_mk δ X.hom n)

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
        (IsPullback.id_horiz i) n (fundamentalClass_mk δ X.hom n) := sorry

/-- The derived module `i_* 𝒪_Z` vanishes on the open complement of a closed immersion. -/
theorem pushforwardStructureSheaf_restrictAway_isZero
    {Z X : Scheme.{u}} (i : Z ⟶ X) [hclosed : IsClosedImmersion i] :
    IsZero (restrictAway i
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X i
        (@instQuasiCompactOfIsClosedImmersion Z X i hclosed) inferInstance).obj) :=
  sorry

/-- For a regular closed immersion, `i_* 𝒪_Z` is a perfect derived module. -/
theorem pushforwardStructureSheaf_isPerfect
    {Z X : Scheme.{u}} (i : Z ⟶ X) [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i] :
    RingedSpace.ModuleDerived.IsPerfect
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X i
        (@instQuasiCompactOfIsClosedImmersion Z X i hclosed) inferInstance).obj :=
  sorry

/-- Quasi-compactness of `X`, or of its irreducible components, supplies the localized-Chern
technical condition for `i_* 𝒪_Z`. -/
theorem pushforwardStructureSheaf_technicalCondition
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [hclosed : IsClosedImmersion i]
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) :
    TechnicalCondition X
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj :=
  sorry

/-- The pushed-forward structure sheaf of a regular closed immersion satisfies the
rank-bounded localized-Chern hypotheses in every positive degree. -/
theorem pushforwardStructureSheaf_rankBound
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (t : ℕ) (ht : 0 < t) :
    Situation S δ X i
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj
      t .rankBound := sorry

/-- The pushed-forward structure sheaf of a regular closed immersion satisfies the
vanishing localized-Chern hypotheses in every degree. -/
theorem pushforwardStructureSheaf_vanishing
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [LocallyOfFiniteType (i ≫ X.hom)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (hX : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (t : ℕ) :
    Situation S δ X i
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj
      t .vanishing := sorry

/-- The identity-horizontal cap of the degree-`t` localized Chern character of `i_* 𝒪_Z`
against `[X]_n`, realized as the Newton-class cap tensored with `(t!)⁻¹`. -/
noncomputable def characterCapOnFundamental
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [hclosed : IsClosedImmersion i] [LocallyOfFiniteType (i ≫ X.hom)]
    (classes : ChernClass.Theory δ X.hom)
    (perfect : RingedSpace.ModuleDerived.IsPerfect
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj)
    (vanishing : IsZero (restrictAway i
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj))
    (finiteness : TechnicalCondition X
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj)
    (t : ℕ) (n : ℤ) :
    TensorProduct ℤ (RelativeChow δ (Over.mk (i ≫ X.hom)) (n - (t : ℤ))) ℚ :=
  let E := (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
    (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj
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
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj)
    (vanishing : IsZero (restrictAway i
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj))
    (finiteness : TechnicalCondition X
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj)
    (t : ℕ) (n : ℤ) :
    characterCapOnFundamental i classes perfect vanishing finiteness t n =
      let E := (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
        (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj
      TensorProduct.tmul ℤ
        (capOnFundamental X i (newtonClass i classes E perfect vanishing finiteness t) n)
        ((t.factorial : ℚ)⁻¹) := sorry

/-- Lemma 42.55.4 (1): in the situation of Lemma 42.55.3, if `dim_δ(X) = n`, then
`c_t(Z ⟶ X, i_* 𝒪_Z) ∩ [X]_n = 0` for `0 < t < r`. -/
@[stacks 0FEH]
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
    let E := (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
      (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj
    let setup := pushforwardStructureSheaf_rankBound δ i hX t ht
    capOnFundamental X i
      (chernClass i classes E setup.perfect t setup.offCenter setup.finiteness) n = 0 := sorry

/-- Lemma 42.55.4 (2): in the situation of Lemma 42.55.3, if `dim_δ(X) = n`, then
`c_r(Z ⟶ X, i_* 𝒪_Z) ∩ [X]_n = (-1)^(r - 1) * (r - 1)! • [Z]_{n - r}`. -/
@[stacks 0FEH]
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
    let E := (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X.left i
      (@instQuasiCompactOfIsClosedImmersion Z X.left i hclosed) inferInstance).obj
    let setup := pushforwardStructureSheaf_rankBound δ i hX r hr
    capOnFundamental X i
      (chernClass i classes E setup.perfect r setup.offCenter setup.finiteness) n =
      (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ)) •
        fundamentalClass_mk δ (i ≫ X.hom) (n - (r : ℤ)) := sorry

/-- Lemma 42.55.4 (3): in the situation of Lemma 42.55.3, if `dim_δ(X) = n`, then
`ch_t(Z ⟶ X, i_* 𝒪_Z) ∩ [X]_n = 0` for `t < r`, including `t = 0`. -/
@[stacks 0FEH]
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
      (pushforwardStructureSheaf_isPerfect i)
      (pushforwardStructureSheaf_restrictAway_isZero i)
      (pushforwardStructureSheaf_technicalCondition i hX) t n = 0 := sorry

/-- Lemma 42.55.4 (4): in the situation of Lemma 42.55.3, if `dim_δ(X) = n`, then
`ch_r(Z ⟶ X, i_* 𝒪_Z) ∩ [X]_n = [Z]_{n - r}`. -/
@[stacks 0FEH]
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
      (X.hom.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt))
    (hr : 0 < r) :
    characterCapOnFundamental i classes
      (pushforwardStructureSheaf_isPerfect i)
      (pushforwardStructureSheaf_restrictAway_isZero i)
      (pushforwardStructureSheaf_technicalCondition i hX) r n =
      TensorProduct.tmul ℤ (fundamentalClass_mk δ (i ≫ X.hom) (n - (r : ℤ))) (1 : ℚ) :=
  sorry

end AlgebraicGeometry.LocalizedChern
