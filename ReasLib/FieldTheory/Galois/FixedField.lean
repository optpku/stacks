/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Inclusions between fixed fields

This leaf packages the contravariant algebra map on fixed fields induced by an inclusion of
subgroups.  Naming the construction avoids repeatedly unfolding `IntermediateField.inclusion`
when a tower of fixed fields is used downstream.
@stack 0BU6
-/

universe u v

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/-- A subgroup inclusion `H ≤ H'` induces the canonical algebra structure of `E^H` over
`E^H'`. -/
@[reducible, stacks 0BU6 "fixed-field algebra map along subgroup inclusion"]
def fixedFieldAlgebraOfLe {H H' : Subgroup Gal(E / F)} (h : H ≤ H') :
    Algebra (fixedField H') (fixedField H) :=
  ((inclusion (fixedField_le h)).toRingHom).toAlgebra

/-- The algebra map of `fixedFieldAlgebraOfLe` is the canonical intermediate-field inclusion. -/
@[stacks 0BU6 "algebra map of the fixed-field inclusion"]
theorem algebraMap_fixedFieldAlgebraOfLe {H H' : Subgroup Gal(E / F)} (h : H ≤ H') :
    @algebraMap (fixedField H') (fixedField H) _ _ (fixedFieldAlgebraOfLe h) =
      (inclusion (fixedField_le h)).toRingHom := sorry

-- Proof strategy: unfold `fixedFieldAlgebraOfLe`; the algebra map of
-- `RingHom.toAlgebra` is definitionally the ring homomorphism induced by the intermediate-field
-- inclusion.

section FiniteGalois

variable [FiniteDimensional F E] [IsGalois F E]

/-- The canonical inclusion tower `E^H' → E^H → E` is compatible for `H ≤ H'`. -/
@[stacks 0BU6 "scalar tower for nested fixed fields"]
theorem fixedField_isScalarTower_of_le {H H' : Subgroup Gal(E / F)} (h : H ≤ H') :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    IsScalarTower (fixedField H') (fixedField H) E := sorry

-- Proof strategy: install `fixedFieldAlgebraOfLe h`, rewrite its algebra map with
-- `algebraMap_fixedFieldAlgebraOfLe`, and prove the scalar-tower algebra-map identity by
-- extensionality in the ambient field `E`.

/-- If `H` is normal in `H'`, then `E^H / E^H'` is a normal extension.  The displayed algebra
structure is the canonical inclusion selected by `fixedFieldAlgebraOfLe`. -/
@[stacks 0BU6 "normality between nested fixed fields"]
theorem fixedField_normal_of_normal {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    Normal (fixedField H') (fixedField H) := sorry

-- Proof strategy: use the finite Galois correspondence: normality of `H` inside `H'` makes the
-- fixed field of `H` normal over the fixed field of `H'`.  Pin the named inclusion and scalar
-- tower, then specialize Mathlib's normal-fixed-field theorem to the subgroup `H.subgroupOf H'`.

/-- If `H` is normal in `H'`, the relative fixed-field extension `E^H / E^H'` is Galois. -/
@[stacks 0BU6 "Galois extension between nested fixed fields"]
theorem fixedField_isGalois_of_normal {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    IsGalois (fixedField H') (fixedField H) := sorry

-- Proof strategy: install `fixedField_isScalarTower_of_le` and
-- `fixedField_normal_of_normal`; finite-dimensionality and separability descend to intermediate
-- fields, so the standard `IsGalois` constructor gives the relative fixed-field extension.

/-- Restriction of `H'` to `E^H`, viewed as automorphisms over `E^H'`.

The local algebra and normality instances are definitional pins for the canonical fixed-field
inclusion; they are not ambient competing instances. -/
@[reducible, stacks 0BU6 "restriction homomorphism between nested fixed fields"]
noncomputable def fixedFieldRestrictHom {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    H' →* Gal(fixedField H / fixedField H') :=
  letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
  letI : IsScalarTower (fixedField H') (fixedField H) E :=
    fixedField_isScalarTower_of_le h
  letI : Normal (fixedField H') (fixedField H) := fixedField_normal_of_normal h
  (AlgEquiv.restrictNormalHom (fixedField H)).comp
    (subgroupEquivAlgEquiv H').toMonoidHom

/-- The subgroup `H`, regarded as a subgroup of `H'`, lies in the kernel of restriction to
`E^H`. -/
@[stacks 0BU6 "kernel inclusion for nested fixed-field restriction"]
theorem subgroupOf_le_ker_fixedFieldRestrictHom
    {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    H.subgroupOf H' ≤ (fixedFieldRestrictHom h).ker := sorry

-- Proof strategy: unfold membership in `H.subgroupOf H'` and the kernel.  Elements of `H` fix
-- every element of `fixedField H`; evaluate `AlgEquiv.restrictNormalHom` on an arbitrary fixed
-- element and use `IntermediateField.mem_fixedField_iff`.

/-- The kernel of restriction from `H'` to `Gal(E^H/E^H')` is exactly `H`. -/
@[stacks 0BU6 "kernel of nested fixed-field restriction"]
theorem fixedFieldRestrictHom_ker {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    (fixedFieldRestrictHom h).ker = H.subgroupOf H' := sorry

-- Proof strategy: rewrite the kernel of `AlgEquiv.restrictNormalHom` with
-- `IntermediateField.restrictNormalHom_ker`, then identify the fixing subgroup of
-- `fixedField H` with `H` using `IntermediateField.fixingSubgroup_fixedField`; transport the
-- result through `subgroupEquivAlgEquiv H'`.

/-- Restriction from `H'` onto `Gal(E^H/E^H')` is surjective. -/
@[stacks 0BU6 "surjectivity of nested fixed-field restriction"]
theorem fixedFieldRestrictHom_surjective
    {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    Function.Surjective (fixedFieldRestrictHom h) := sorry

-- Proof strategy: apply `AlgEquiv.restrictNormalHom_surjective` to the normal relative extension
-- `fixedField H / fixedField H'`; use the Galois correspondence to lift the resulting ambient
-- automorphism to an element of `H'` and simplify the defining composite.

/-- The restriction homomorphism descends canonically from `H' / H` to
`Gal(E^H/E^H')`. -/
@[reducible, stacks 0BU6 "quotient homomorphism for nested fixed fields"]
noncomputable def fixedFieldQuotientHom {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    H' ⧸ H.subgroupOf H' →* Gal(fixedField H / fixedField H') :=
  letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
  QuotientGroup.lift (H.subgroupOf H') (fixedFieldRestrictHom h)
    (subgroupOf_le_ker_fixedFieldRestrictHom h)

/-- The quotient restriction map identifies `H' / H` with `Gal(E^H/E^H')`. -/
@[stacks 0BU6 "bijectivity of the nested fixed-field quotient map"]
theorem fixedFieldQuotientHom_bijective
    {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    Function.Bijective (fixedFieldQuotientHom h) := sorry

-- Proof strategy: use `QuotientGroup.injective_lift_iff` with
-- `fixedFieldRestrictHom_ker` for injectivity and
-- `QuotientGroup.lift_surjective_of_surjective` with
-- `fixedFieldRestrictHom_surjective` for surjectivity.

/-- The Galois group of `E^H / E^H'` and the quotient `H' / H` have the same cardinality. -/
@[stacks 0BU6 "cardinality of the nested fixed-field Galois group"]
theorem natCard_gal_fixedField_eq_quotient
    {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    Nat.card (Gal(fixedField H / fixedField H')) =
      Nat.card (H' ⧸ H.subgroupOf H') := sorry

-- Proof strategy: apply `Nat.card_congr` to the equivalence obtained from
-- `Equiv.ofBijective (fixedFieldQuotientHom h) (fixedFieldQuotientHom_bijective h)` and orient
-- the resulting equality as displayed.

/-- On quotient representatives, the fixed-field quotient map is the restriction homomorphism. -/
@[stacks 0BU6 "nested fixed-field quotient map on representatives"]
theorem fixedFieldQuotientHom_mk
    {H H' : Subgroup Gal(E / F)} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] (sigma : H') :
    letI : Algebra (fixedField H') (fixedField H) := fixedFieldAlgebraOfLe h
    fixedFieldQuotientHom h (QuotientGroup.mk sigma) = fixedFieldRestrictHom h sigma := sorry

-- Proof strategy: unfold `fixedFieldQuotientHom` and apply `QuotientGroup.lift_mk`; no choice of
-- quotient representative is involved.

end FiniteGalois

end IntermediateField
