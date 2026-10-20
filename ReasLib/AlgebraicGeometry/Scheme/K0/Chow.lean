/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.TotalCap
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.ChernCharacter

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

open AlgebraicGeometry.ChowGroup AlgebraicGeometry.Scheme.K0WithSupport

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
            chernCharacterWithTheory δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite) :
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      rationalChow δ (Over.mk (i ≫ Y.hom)) where
  toFun a :=
    capRationalCompletion δ i
      (chernCharacterWithTheory δ i hqc classes (toK0WithSupport i a))
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
            chernCharacterWithTheory δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite)
    (a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) :
    toRationalChow δ i hqc classes hfin a =
      capRationalCompletion δ i
        (chernCharacterWithTheory δ i hqc classes (toK0WithSupport i a))
        (hfin a).toFinset :=
  sorry

/-- The `ℚ`-linear extension `K₀'(Z) ⊗ ℚ → CH_*(Z) ⊗ ℚ` of `toRationalChow`. -/
noncomputable def toRationalChow_tensorQ
    (hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left))
    (classes : ChernClass.Theory δ Y.hom)
    (hfin :
      ∀ a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i),
        {p : ℕ |
            chernCharacterWithTheory δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite) :
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
            chernCharacterWithTheory δ i hqc classes (toK0WithSupport i a) p ≠ 0}.Finite)
    (a : @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i)) (q : ℚ) :
    toRationalChow_tensorQ δ i hqc classes hfin (a ⊗ₜ[ℤ] q) =
      smulRationalChow δ (Over.mk (i ≫ Y.hom)) q
        (toRationalChow δ i hqc classes hfin a) :=
  sorry

/-- The rational coherent K-theory comparison obtained from degree-zero realization,
the canonical localized Chern character, and cap against the ambient fundamental class. -/
noncomputable def canonicalToRationalChow_tensorQ
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsClosedImmersion i.left] [Scheme.Regular Y.left]
    [CompactSpace Y.left] :
    TensorProduct ℤ (@K0' X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)) ℚ →+
      rationalChow δ X :=
  let hqc : ∀ C : irreducibleComponents Y.left, IsCompact (C : Set Y.left) :=
    fun C ↦ (isClosed_of_mem_irreducibleComponents C.val C.property).isCompact
  let classes := ChernClass.Theory.canonical δ Y.hom
  (rationalChow.congrHom δ (i.left ≫ Y.hom) (Over.w i)).toAddMonoidHom.comp
    (toRationalChow_tensorQ δ i.left hqc classes
      (fun a ↦ chernCharacterWithTheory_finiteSupport δ i.left hqc classes
        inferInstance (toK0WithSupport i.left a)))

/-- A closed immersion into a regular quasi-compact scheme gives a bijective rational
comparison from coherent K-theory to total Chow homology via the canonical Chern character. -/
theorem toRationalChow_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsClosedImmersion i.left] [Scheme.Regular Y.left]
    [CompactSpace Y.left] :
    Function.Bijective (canonicalToRationalChow_tensorQ δ i) :=
  sorry

end AlgebraicGeometry.Scheme.K0'
