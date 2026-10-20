module

public import Mathlib.Algebra.Group.Equiv.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.Algebra.KTheory.Milnor.DegreeZero

@[expose] public section

open AlgebraicGeometry Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.Pointwise

variable {X : Scheme.{u}}

/-- The unrestricted product of degree-zero Milnor K-groups of residue fields of
points of weight `k`. -/
abbrev Coefficients (d : X → ℤ) (k : ℤ) : Type u :=
  (x : {x : X // d x = k}) → MilnorK.Group 0 (X.residueField x.1)

/-- Pointwise identification of integer coefficients with degree-zero Milnor K-coefficients
on the weight-`k` locus. -/
def coefficientsEquiv (d : X → ℤ) (k : ℤ) :
    ((x : {x : X // d x = k}) → ℤ) ≃+ Coefficients d k :=
  AddEquiv.piCongrRight fun x ↦ MilnorK.degreeZeroEquiv (X.residueField x.1)

/-- A coefficient family is locally finite when every quasi-compact open meets only
finitely many nonzero terms. -/
def IsLocallyFinite {d : X → ℤ} {k : ℤ} (n : Coefficients d k) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → {x | x.1 ∈ U ∧ n x ≠ 0}.Finite

/-- The zero coefficient family is locally finite. -/
private theorem zero_isLocallyFinite (d : X → ℤ) (k : ℤ) :
    IsLocallyFinite (0 : Coefficients d k) := sorry

/-- Addition preserves local finiteness of coefficient families. -/
private theorem add_isLocallyFinite {d : X → ℤ} {k : ℤ} {a b : Coefficients d k}
    (ha : IsLocallyFinite a) (hb : IsLocallyFinite b) :
    IsLocallyFinite (a + b) := sorry

/-- Negation preserves local finiteness of coefficient families. -/
private theorem neg_isLocallyFinite {d : X → ℤ} {k : ℤ} {a : Coefficients d k}
    (ha : IsLocallyFinite a) : IsLocallyFinite (-a) := sorry

/-- The subgroup of locally finite families in the unrestricted product of degree-zero
Milnor K-groups of residue fields. -/
@[no_expose] def locallyFinite (d : X → ℤ) (k : ℤ) : AddSubgroup (Coefficients d k) where
  carrier := {n | IsLocallyFinite n}
  zero_mem' := zero_isLocallyFinite d k
  add_mem' := add_isLocallyFinite
  neg_mem' := neg_isLocallyFinite

/-- Membership in the locally finite subgroup is local finiteness of the coefficient family. -/
theorem mem_locallyFinite_iff {d : X → ℤ} {k : ℤ} (n : Coefficients d k) :
    n ∈ locallyFinite d k ↔ IsLocallyFinite n := Iff.rfl

/-- Pointwise degree-zero Milnor K-coefficients of a cycle supported in weight `k`. -/
def toCoefficients (d : X → ℤ) (k : ℤ) (α : CycleGroup X d k) :
    Coefficients d k :=
  coefficientsEquiv d k fun x ↦ toAlgebraicCycle d k α x.1

/-- Extend a coefficient family by its integer augmentation on the weight-`k` locus
and by zero elsewhere. -/
def fromCoefficients (d : X → ℤ) (k : ℤ) (n : Coefficients d k) : X → ℤ :=
  fun x ↦ if h : d x = k then (coefficientsEquiv d k).symm n ⟨x, h⟩ else 0

/-- The coefficients of a cycle form a locally finite family. -/
private theorem toCoefficients_isLocallyFinite (d : X → ℤ) (k : ℤ)
    (α : CycleGroup X d k) : IsLocallyFinite (toCoefficients d k α) := sorry

/-- The integer extension of a locally finite coefficient family has locally finite support. -/
private theorem fromCoefficients_locallyFiniteSupport (d : X → ℤ) (k : ℤ)
    (n : Coefficients d k) (hn : IsLocallyFinite n) :
    LocallyFiniteSupport (fromCoefficients d k n) := sorry

/-- The integer extension of a coefficient family vanishes off the weight-`k` locus. -/
private theorem fromCoefficients_dimension (d : X → ℤ) (k : ℤ)
    (n : Coefficients d k) :
    ∀ x, fromCoefficients d k n x ≠ 0 → d x = k := sorry

/-- A locally finite coefficient family defines a cycle supported in weight `k`. -/
private def fromLocallyFinite (d : X → ℤ) (k : ℤ) (n : locallyFinite d k) :
    CycleGroup X d k :=
  ⟨{ toFun := fromCoefficients d k n.1
     supportWithinDomain' := subset_univ _
     supportLocallyFiniteWithinDomain' :=
       fun x _ ↦ fromCoefficients_locallyFiniteSupport d k n.1 n.2 x },
    (AlgebraicCycle.mem_dimensionSubgroup d k _).mpr (fromCoefficients_dimension d k n.1)⟩

/-- Reconstructing a cycle from its degree-zero coefficients recovers the cycle. -/
private theorem fromLocallyFinite_toCoefficients (d : X → ℤ) (k : ℤ)
    (α : CycleGroup X d k) :
    fromLocallyFinite d k ⟨toCoefficients d k α, toCoefficients_isLocallyFinite d k α⟩ = α :=
  sorry

/-- Taking coefficients of the cycle of a locally finite family recovers that family. -/
private theorem toCoefficients_fromLocallyFinite (d : X → ℤ) (k : ℤ)
    (n : locallyFinite d k) : toCoefficients d k (fromLocallyFinite d k n) = n.1 := sorry

/-- Taking degree-zero coefficients preserves addition of cycles. -/
private theorem toCoefficients_add (d : X → ℤ) (k : ℤ) (α β : CycleGroup X d k) :
    toCoefficients d k (α + β) = toCoefficients d k α + toCoefficients d k β := sorry

/-- Cycles supported in weight `k` are additively equivalent to locally finite families
of degree-zero Milnor K-coefficients on the weight-`k` locus. -/
@[no_expose] def equiv (d : X → ℤ) (k : ℤ) : CycleGroup X d k ≃+ locallyFinite d k where
  toFun α := ⟨toCoefficients d k α, toCoefficients_isLocallyFinite d k α⟩
  invFun := fromLocallyFinite d k
  left_inv := fromLocallyFinite_toCoefficients d k
  right_inv n := Subtype.ext (toCoefficients_fromLocallyFinite d k n)
  map_add' α β := Subtype.ext (toCoefficients_add d k α β)

/-- Evaluating the coefficient presentation on a cycle is pointwise `degreeZeroMap`. -/
theorem equiv_apply (d : X → ℤ) (k : ℤ) (α : CycleGroup X d k)
    (x : {x : X // d x = k}) :
    (equiv d k α).1 x =
      MilnorK.degreeZeroMap (X.residueField x.1) (toAlgebraicCycle d k α x.1) := by rfl

/-- The inverse coefficient presentation recovers integers by degree-zero augmentation
on the weight-`k` locus and by zero elsewhere. -/
theorem equiv_symm_apply (d : X → ℤ) (k : ℤ) (n : locallyFinite d k) (x : X) :
    toAlgebraicCycle d k ((equiv d k).symm n) x =
      if h : d x = k then
        (MilnorK.degreeZeroEquiv (X.residueField x)).symm (n.1 ⟨x, h⟩)
      else
        0 := by rfl

end AlgebraicGeometry.CycleGroup.Pointwise
