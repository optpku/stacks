/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Frobenius.Subfield
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Frobenius composita

@stack 07P1
@stack 07P2
@stack 07P4

The compositum of a base field and the Frobenius subfield is a Frobenius construction, not a
p-basis-specific object.  This neutral owner is the canonical source for both the p-basis
compatibility view and finite-extension descent.
-/

@[expose] public section

universe u v w

namespace FieldExtension.Frobenius

/-- The compositum of a base field with the `p`-th-power subfield of `K`. -/
@[stacks 07P1 "p-power compositum"]
abbrev compositum (p : ℕ) (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [ExpChar K p] : IntermediateField k K :=
  IntermediateField.adjoin k (subfield p K : Set K)

/-- The ambient field is purely inseparable over its Frobenius compositum. -/
@[stacks 07P2 "ambient field purely inseparable over its Frobenius compositum"]
instance compositum.isPurelyInseparable {p : ℕ} {k : Type u} {K : Type v}
    [Field k] [Field K] [Algebra k K] [ExpChar K p] :
    IsPurelyInseparable (compositum p k K) K := by
  rw [isPurelyInseparable_iff_pow_mem (compositum p k K) p]
  intro x
  refine ⟨1, ?_⟩
  simp only [pow_one]
  exact ⟨⟨x ^ p,
    IntermediateField.subset_adjoin k (subfield p K : Set K) (pow_mem p K x)⟩, rfl⟩
/- Proof strategy: apply `isPurelyInseparable_iff_pow_mem (compositum p k K) p`; for each
`x : K`, choose exponent `1` and use `IntermediateField.subset_adjoin` to put `x ^ p` in the
algebra-map range of the compositum. -/

/- The subfield containment form is the bridge used when the base is an intermediate field. -/
/-- Frobenius containment makes the ambient field purely inseparable over an intermediate field. -/
@[stacks 07P2 "purely inseparable extension from Frobenius containment"]
theorem isPurelyInseparable_of_subfield_le {p : ℕ} {k : Type u} {K : Type v}
    [Field k] [Field K] [Algebra k K] [ExpChar K p] (L : IntermediateField k K)
    (hF : subfield p K ≤ L.toSubfield) : IsPurelyInseparable L K := by
  rw [isPurelyInseparable_iff_pow_mem L p]
  intro x
  refine ⟨1, ?_⟩
  simp only [pow_one]
  exact ⟨⟨x ^ p, hF (pow_mem p K x)⟩, rfl⟩
/- Proof strategy: apply `isPurelyInseparable_iff_pow_mem L p`; for each `x : K`, choose exponent
`1` and use `hF` to put `x ^ p` in the algebra-map range of `L`. -/

/-- The subfield generated in `L` by `Lᵖ` and the image of a subfield of the base. -/
@[stacks 07P4 "Frobenius compositum after scalar extension"]
abbrev compositumMap {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : ℕ) (k : Subfield K) [ExpChar L p] : Subfield L :=
  subfield p L ⊔ k.map (algebraMap K L)

/- The named inclusion is useful for consumers working with the `IntermediateField` presentation;
the scalar-extended `Subfield` companion below handles the mapped-base presentation. -/
/-- The Frobenius subfield is contained in the compositum with any base field. -/
@[stacks 07P1 "Frobenius summand in the p-power compositum"]
theorem subfield_le_compositum (p : ℕ) (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] [ExpChar K p] :
    subfield p K ≤ (compositum p k K).toSubfield := by
  intro x hx
  exact IntermediateField.subset_adjoin k (subfield p K : Set K) hx
/- Proof strategy: unfold `compositum` and apply `IntermediateField.subset_adjoin` to the
Frobenius-range generators. -/

/-- The Frobenius summand is contained in a scalar-extended compositum. -/
@[stacks 07P4 "Frobenius summand of a scalar-extended compositum"]
theorem subfield_le_compositumMap {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (p : ℕ) (k : Subfield K) [ExpChar L p] :
    subfield p L ≤ compositumMap p k := le_sup_left
/- Proof strategy: unfold `compositumMap` and apply `le_sup_left`. -/

/-- The `IntermediateField` and `Subfield` presentations of a scalar-extended compositum agree. -/
@[stacks 07P4 "IntermediateField-to-Subfield compositum bridge"]
theorem compositum_toSubfield_eq_compositumMap {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (p : ℕ) (k : Subfield K) [ExpChar L p] :
    (compositum p (k.map (algebraMap K L)) L).toSubfield = compositumMap p k := by
  rw [IntermediateField.adjoin_toSubfield, Subfield.closure_union]
  change
    Subfield.closure ((algebraMap (k.map (algebraMap K L)) L).fieldRange : Set L) ⊔
        Subfield.closure ((_root_.frobenius L p).fieldRange : Set L) =
      (_root_.frobenius L p).fieldRange ⊔ k.map (algebraMap K L)
  rw [Subfield.closure_eq, Subfield.closure_eq]
  have hrange :
      (algebraMap (k.map (algebraMap K L)) L).fieldRange = k.map (algebraMap K L) := by
    ext x
    change (∃ y : k.map (algebraMap K L), (y : L) = x) ↔ x ∈ k.map (algebraMap K L)
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange, sup_comm]
/- Proof strategy: rewrite `IntermediateField.adjoin_toSubfield` and identify the image of the
subtype algebra map with `k.map (algebraMap K L)` using `Subfield.map` extensionality. -/

/-- Frobenius composita commute with a tower of scalar extensions. -/
@[stacks 07P4 "tower law for scalar-extended Frobenius composita"]
theorem compositumMap_map_eq {K : Type u} {M : Type v} {L : Type w}
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (p : ℕ) (k : Subfield K) [ExpChar M p] [ExpChar L p] :
    compositumMap (K := M) (L := L) p
        (compositumMap (K := K) (L := M) p k) =
      compositumMap (K := K) (L := L) p k := by
  have hF : (subfield p M).map (algebraMap M L) ≤ subfield p L := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := (mem_subfield_iff p M).mp hx
    apply (mem_subfield_iff p L).mpr
    exact ⟨algebraMap M L z, by rw [← map_pow, hz]⟩
  change
    subfield p L ⊔
        (subfield p M ⊔ k.map (algebraMap K M)).map (algebraMap M L) =
      subfield p L ⊔ k.map (algebraMap K L)
  rw [Subfield.map_sup, Subfield.map_map, IsScalarTower.algebraMap_eq K M L,
    ← sup_assoc, sup_eq_left.mpr hF]
/- Proof strategy: expand both `compositumMap` terms, use `Subfield.map_sup` and `map_map`, and
identify the image of the intermediate Frobenius subfield with the Frobenius subfield of `L`. -/

end FieldExtension.Frobenius
