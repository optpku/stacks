/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Comparison
public import stacks_project.Chap42.Lemma_42_55_4
public import stacks_project.Chap42.Remark_42_56_11_ChernCharacter

/-!
# Localized Chern character capped on the fundamental class

This file packages the composition `K₀'(X) → K₀(D_{X,perf}(O_Y)) → A^*(X ⟶ Y) ⊗ ℚ →
CH_*(X) ⊗ ℚ` of `ℱ ↦ ℱ[0]`, the localized Chern character `ch(X ⟶ Y, -)`, and
`c ↦ c ∩ [Y]`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.BivariantClass.Nonnegative
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Rational total Chow homology `CH_*(X) ⊗ ℚ`. -/
abbrev rationalChow {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] : Type u :=
  TensorProduct ℤ (Total δ X) ℚ

/-- `rationalChow` is the tensor product of total relative Chow homology with `ℚ`. -/
theorem rationalChow_def {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] :
    rationalChow δ X = TensorProduct ℤ (Total δ X) ℚ :=
  sorry

/-- Relative dimensions of generic points of a quasi-compact locally finite-type scheme. -/
noncomputable def relativeDimensionDegrees {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] : Finset ℤ :=
  let hNoeth : IsNoetherian X.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  (genericPoints.finite
      (@finite_irreducibleComponents_of_isNoetherian X.left hNoeth)).toFinset.image
    (X.hom.relativeDimensionFunction δ)

/-- `relativeDimensionDegrees` is the image of the finite set of generic points under the
relative dimension function. -/
theorem relativeDimensionDegrees_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] :
    relativeDimensionDegrees δ X =
      (genericPoints.finite
          (@finite_irreducibleComponents_of_isNoetherian X.left
            { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom })).toFinset.image
        (X.hom.relativeDimensionFunction δ) :=
  sorry

/-- The total fundamental class `[Y] ∈ CH_*(Y)` assembled from the degree-`n` pieces
`[Y]_n` on the finitely many relative dimensions of generic points. -/
noncomputable def totalFundamentalClass {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    [CompactSpace Y.left] : Total δ Y :=
  ∑ n ∈ relativeDimensionDegrees δ Y,
    DirectSum.of _ n (fundamentalClass_mk δ Y.hom n)

/-- The degree-`n` summand of `totalFundamentalClass` is `[Y]_n`. -/
theorem totalFundamentalClass_of {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    [CompactSpace Y.left] (n : ℤ) :
    (totalFundamentalClass δ Y n) =
      if n ∈ relativeDimensionDegrees δ Y then fundamentalClass_mk δ Y.hom n else 0 :=
  sorry

/-- Identity-horizontal cap of a homogeneous bivariant class against `[Y]_n`. -/
noncomputable def capOnFundamentalHom {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] (p n : ℤ) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) p →+
      RelativeChow δ (Over.mk (i ≫ Y.hom)) (n - p) where
  toFun c := LocalizedChern.capOnFundamental Y i c n
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of `capOnFundamentalHom` is `LocalizedChern.capOnFundamental`. -/
theorem capOnFundamentalHom_apply {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] {p n : ℤ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y) p) :
    capOnFundamentalHom Y i p n c =
      LocalizedChern.capOnFundamental Y i c n :=
  sorry

/-- Cap a completed rational bivariant class with finite Chern support against the
fundamental class of `Y`, landing in `CH_*(X) ⊗ ℚ`. -/
noncomputable def capRationalCompletion {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {Y : Over S} [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] [CompactSpace Y.left]
    (c : RationalCompletion δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y))
    (s : Finset ℕ) : rationalChow δ (Over.mk (i ≫ Y.hom)) :=
  ∑ p ∈ s,
    ∑ n ∈ relativeDimensionDegrees δ Y,
      TensorProduct.map
        (DirectSum.lof ℤ ℤ
          (fun d ↦ RelativeChow δ (Over.mk (i ≫ Y.hom)) d) (n - (p : ℤ)))
        (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
        (TensorProduct.map (capOnFundamentalHom Y i (p : ℤ) n).toIntLinearMap
          (LinearMap.id : ℚ →ₗ[ℤ] ℚ) (c p))

/-- `capRationalCompletion` is the double sum of identity-horizontal caps of the
finite-support Chern components against `[Y]_n`. -/
theorem capRationalCompletion_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {Y : Over S} [LocallyOfFiniteType Y.hom]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ Y.hom)] [CompactSpace Y.left]
    (c : RationalCompletion δ (Over.homMk i : Over.mk (i ≫ Y.hom) ⟶ Y))
    (s : Finset ℕ) :
    capRationalCompletion δ i c s =
      ∑ p ∈ s,
        ∑ n ∈ relativeDimensionDegrees δ Y,
          TensorProduct.map
            (DirectSum.lof ℤ ℤ
              (fun d ↦ RelativeChow δ (Over.mk (i ≫ Y.hom)) d) (n - (p : ℤ)))
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
            (TensorProduct.map (capOnFundamentalHom Y i (p : ℤ) n).toIntLinearMap
              (LinearMap.id : ℚ →ₗ[ℤ] ℚ) (c p)) :=
  sorry

/-- Scale a rational Chow class by a rational number on the `ℚ` factor. -/
noncomputable def smulRationalChow {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (q : ℚ) : rationalChow δ X →+ rationalChow δ X :=
  (TensorProduct.map (LinearMap.id : Total δ X →ₗ[ℤ] Total δ X)
      (AddMonoidHom.mulLeft q).toIntLinearMap).toAddMonoidHom

/-- `smulRationalChow` scales the `ℚ` factor of a rational Chow class. -/
theorem smulRationalChow_apply {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (q : ℚ) (x : rationalChow δ X) :
    smulRationalChow δ X q x =
      (TensorProduct.map (LinearMap.id : Total δ X →ₗ[ℤ] Total δ X)
          (AddMonoidHom.mulLeft q).toIntLinearMap) x :=
  sorry

/-- Transport `CH_* ⊗ ℚ` along an equality of structure morphisms over `S`. -/
noncomputable def rationalChow.congrHom {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {X : Over S}
    [LocallyOfFiniteType X.hom] (f : X.left ⟶ S)
    [instf : LocallyOfFiniteType f] (h : f = X.hom) :
    rationalChow δ (Over.mk f) ≃+ rationalChow δ X where
  toEquiv :=
    Equiv.cast
      (Eq.rec (motive := fun (g : X.left ⟶ S) (e : f = g) =>
          rationalChow δ (Over.mk f) =
            @rationalChow S inferInstance δ inferInstance (Over.mk g) (e ▸ instf))
        rfl h : rationalChow δ (Over.mk f) = rationalChow δ X)
  map_add' := sorry

/-- Transport along a reflexive equality of structure morphisms is the identity. -/
theorem rationalChow.congrHom_rfl {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] :
    rationalChow.congrHom δ X.hom rfl = AddEquiv.refl (rationalChow δ X) :=
  sorry

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.Scheme.K0'

open AlgebraicGeometry.ChowGroup AlgebraicGeometry.Scheme.K0WithSupport

/-- Quasi-compactness of a scheme implies every irreducible component is compact. -/
theorem irreducibleComponent_isCompact {X : Scheme.{u}} [CompactSpace X]
    (C : irreducibleComponents X) : IsCompact (C : Set X) :=
  sorry

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {Y : Over S} [LocallyOfFiniteType Y.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ Y.left) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ Y.hom)]
variable [Scheme.Regular Y.left] [CompactSpace Y.left]

/-- The composition `ℱ ↦ ℱ[0]`, then `ch(Z ⟶ Y, -)`, then `c ↦ c ∩ [Y]`, as a map
`K₀'(Z) → CH_*(Z) ⊗ ℚ`. -/
noncomputable def toRationalChow
    (hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left))
    (classes : ChernClass.Theory δ Y.hom)
    (hfin :
      ∀ a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i),
        {p : ℕ |
            chernCharacter δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite) :
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      rationalChow δ (Over.mk (i ≫ Y.hom)) where
  toFun a :=
    capRationalCompletion δ i
      (chernCharacter δ i hqc classes (toK0WithSupport i a))
      (hfin a).toFinset
  map_zero' := sorry
  map_add' := sorry

/-- `toRationalChow` evaluates as the finite-support cap of the localized Chern
character of `ℱ[0]`. -/
theorem toRationalChow_apply
    (hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left))
    (classes : ChernClass.Theory δ Y.hom)
    (hfin :
      ∀ a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i),
        {p : ℕ |
            chernCharacter δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite)
    (a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) :
    toRationalChow δ i hqc classes hfin a =
      capRationalCompletion δ i
        (chernCharacter δ i hqc classes (toK0WithSupport i a))
        (hfin a).toFinset :=
  sorry

/-- The `ℚ`-linear extension `K₀'(Z) ⊗ ℚ → CH_*(Z) ⊗ ℚ` of `toRationalChow`. -/
noncomputable def toRationalChow_tensorQ
    (hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left))
    (classes : ChernClass.Theory δ Y.hom)
    (hfin :
      ∀ a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i),
        {p : ℕ |
            chernCharacter δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite) :
    TensorProduct ℤ (@K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) ℚ →+
      rationalChow δ (Over.mk (i ≫ Y.hom)) :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun q =>
            smulRationalChow δ (Over.mk (i ≫ Y.hom)) q
              (toRationalChow δ i hqc classes hfin a)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- On a pure tensor, `toRationalChow_tensorQ` scales `toRationalChow`. -/
theorem toRationalChow_tensorQ_tmul
    (hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left))
    (classes : ChernClass.Theory δ Y.hom)
    (hfin :
      ∀ a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i),
        {p : ℕ |
            chernCharacter δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite)
    (a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) (q : ℚ) :
    toRationalChow_tensorQ δ i hqc classes hfin (a ⊗ₜ[ℤ] q) =
      smulRationalChow δ (Over.mk (i ≫ Y.hom)) q
        (toRationalChow δ i hqc classes hfin a) :=
  sorry

/-- Finite support of `ch(Z ⟶ Y, ℱ[0])`, packaged from quasi-compactness of `Y`. -/
theorem toRationalChow_finiteSupport
    (hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left))
    (classes : ChernClass.Theory δ Y.hom)
    (a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) :
    {p : ℕ |
        chernCharacter δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite :=
  sorry

end AlgebraicGeometry.Scheme.K0'

