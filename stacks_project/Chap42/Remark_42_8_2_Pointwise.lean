/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Equiv.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup
public import stacks_project.Chap42.Remark_42_6_4_Milnor_K_theory_Boundary

@[expose] public section

open AlgebraicGeometry Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.Pointwise

variable {X : Scheme.{u}}

/-- The unrestricted product of degree-zero Milnor K-groups of residue fields of
points of dimension `k`. -/
abbrev Coefficients (d : X → ℤ) (k : ℤ) : Type u :=
  (x : {x : X // d x = k}) → MilnorK.Group 0 (X.residueField x.1)

/-- The canonical additive identification of `ℤ` with `K₀ᴹ(F)`. -/
noncomputable def degreeZeroAddEquiv (F : Type u) [Field F] :
    ℤ ≃+ MilnorK.Group 0 F :=
  AddEquiv.ofBijective (MilnorK.degreeZeroMap F) (MilnorK.degreeZeroMap_bijective F)

/-- Pointwise identification of integer coefficients with `K₀ᴹ` coefficients on the
dimension-`k` locus. -/
noncomputable def coefficientsEquiv (d : X → ℤ) (k : ℤ) :
    ((x : {x : X // d x = k}) → ℤ) ≃+ Coefficients d k :=
  AddEquiv.piCongrRight fun x ↦ degreeZeroAddEquiv (X.residueField x.1)

/-- A family of `K₀ᴹ` coefficients is locally finite when every quasi-compact open of `X`
meets only finitely many nonzero terms. -/
def IsLocallyFinite {d : X → ℤ} {k : ℤ} (n : Coefficients d k) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → {x | x.1 ∈ U ∧ n x ≠ 0}.Finite

/-- The primed sum is the subgroup of locally finite families in the unrestricted
product of `K₀ᴹ(κ(x))`. -/
def locallyFinite (d : X → ℤ) (k : ℤ) : AddSubgroup (Coefficients d k) where
  carrier := {n | IsLocallyFinite n}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the primed sum is local finiteness of the coefficient family. -/
theorem mem_locallyFinite_iff {d : X → ℤ} {k : ℤ} (n : Coefficients d k) :
    n ∈ locallyFinite d k ↔ IsLocallyFinite n := sorry

/-- Pointwise `K₀ᴹ` coefficients of a `k`-cycle. -/
noncomputable def toCoefficients (d : X → ℤ) (k : ℤ) (α : CycleGroup X d k) :
    Coefficients d k :=
  coefficientsEquiv d k fun x ↦ toAlgebraicCycle d k α x.1

/-- Extend a family of `K₀ᴹ` coefficients by `degreeZeroMap.symm` on the dimension-`k`
locus and by `0` off that locus. -/
noncomputable def fromCoefficients (d : X → ℤ) (k : ℤ) (n : Coefficients d k) :
    X → ℤ :=
  fun x ↦ if h : d x = k then (coefficientsEquiv d k).symm n ⟨x, h⟩ else 0

/-- The primed locally finite presentation of the group of `k`-cycles. -/
noncomputable def equiv (d : X → ℤ) (k : ℤ) :
    CycleGroup X d k ≃+ locallyFinite d k where
  toFun α := ⟨toCoefficients d k α, sorry⟩
  invFun n :=
    ⟨{ toFun := fromCoefficients d k n.1
       supportWithinDomain' := subset_univ _
       supportLocallyFiniteWithinDomain' := sorry },
      sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- Evaluating the primed presentation on a `k`-cycle is pointwise `degreeZeroMap`. -/
theorem equiv_apply (d : X → ℤ) (k : ℤ) (α : CycleGroup X d k)
    (x : {x : X // d x = k}) :
    (equiv d k α).1 x =
      MilnorK.degreeZeroMap (X.residueField x.1) (toAlgebraicCycle d k α x.1) := sorry

/-- The inverse primed presentation recovers integer coefficients by `degreeZeroMap.symm`
on the dimension-`k` locus and by `0` elsewhere. -/
theorem equiv_symm_apply (d : X → ℤ) (k : ℤ) (n : locallyFinite d k) (x : X) :
    toAlgebraicCycle d k ((equiv d k).symm n) x =
      if h : d x = k then
        (degreeZeroAddEquiv (X.residueField x)).symm (n.1 ⟨x, h⟩)
      else
        0 := sorry

end AlgebraicGeometry.CycleGroup.Pointwise
