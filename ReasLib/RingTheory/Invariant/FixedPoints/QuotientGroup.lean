/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints.Subalgebra
public import ReasLib.RingTheory.Invariant.Quotient

@[expose] public section

/-!
# Quotient-group actions on fixed subalgebras

For nested subgroups `H ≤ H'`, this leaf packages the canonical action of
`H' ⧸ H.subgroupOf H'` on the `H`-fixed subalgebra.  Keeping the action as explicit named data
lets downstream files select it without installing a competing ambient instance.
@stack 0BU6
-/

universe u v w

open scoped Pointwise

namespace FixedPoints

section Semiring

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommSemiring A] [CommSemiring B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- For `H ≤ H'`, the subgroup `H.subgroupOf H'` has fixed subalgebra `B ^ H` and is a
Galois group for `B / B ^ H`.  This is the bridge from the subgroup-restricted action to the
ambient `H'`-action; Mathlib's direct subgroup instance does not identify these action carriers. -/
@[stacks 0BU6 "subgroup Galois structure for nested fixed subalgebras"]
theorem subgroupOfIsGaloisGroup {H H' : Subgroup G} (h : H ≤ H') :
    IsGaloisGroup (H.subgroupOf H') (FixedPoints.subalgebra A B H) B := sorry

-- Proof strategy: transport Mathlib's canonical `IsGaloisGroup H (B ^ H) B` structure along the
-- group equivalence between `H.subgroupOf H'` and `H`; verify that both actions agree after
-- coercion to the ambient group `G`.

/-- The canonical action of `H' ⧸ H.subgroupOf H'` on the `H`-fixed subalgebra.

Mathlib's canonical `IsGaloisGroup` instance for a subgroup acting on its fixed subalgebra is
used by the bridge above; the action itself is Mathlib's canonical
`IsGaloisGroup.mulSemiringActionQuotient` construction. -/
@[reducible, stacks 0BU6 "quotient action on a fixed subalgebra"]
noncomputable def quotientAction {H H' : Subgroup G} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    MulSemiringAction (H' ⧸ H.subgroupOf H') (FixedPoints.subalgebra A B H) :=
  letI : IsGaloisGroup (H.subgroupOf H') (FixedPoints.subalgebra A B H) B :=
    subgroupOfIsGaloisGroup h
  IsGaloisGroup.mulSemiringActionQuotient H' (FixedPoints.subalgebra A B H) B
    (H.subgroupOf H')

/-- On a representative `σ : H'`, the quotient action becomes the original action after
embedding `B ^ H` into `B`. -/
@[simp, stacks 0BU6 "quotient action on representatives"]
theorem algebraMap_quotientAction_mk {H H' : Subgroup G} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] (σ : H') (x : FixedPoints.subalgebra A B H) :
    letI : MulSemiringAction (H' ⧸ H.subgroupOf H') (FixedPoints.subalgebra A B H) :=
      quotientAction h
    algebraMap (FixedPoints.subalgebra A B H) B
        ((σ : H' ⧸ H.subgroupOf H') • x) =
      σ • algebraMap (FixedPoints.subalgebra A B H) B x := sorry

-- Proof strategy: unfold `quotientAction` and use the representative computation rule for
-- `IsGaloisGroup.mulSemiringActionQuotient`; the transported subgroup action evaluates through
-- the coercion `H' → G`.

/-- The elements of `B ^ H` fixed by the quotient `H' / H` are exactly those coming from
`B ^ H'`. -/
@[stacks 0BU6 "invariants of the quotient action on fixed subalgebras"]
theorem quotientIsInvariant {H H' : Subgroup G} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
      subalgebraAlgebraOfLe h
    letI : MulSemiringAction (H' ⧸ H.subgroupOf H') (FixedPoints.subalgebra A B H) :=
      quotientAction h
    Algebra.IsInvariant (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H)
      (H' ⧸ H.subgroupOf H') := sorry

-- Proof strategy: characterize elements fixed by the quotient action.  Lift each quotient class
-- to `σ : H'`, rewrite its action with `algebraMap_quotientAction_mk`, and identify being fixed by
-- every `σ` with membership in `FixedPoints.subalgebra A B H'`; use
-- `subalgebraAlgebraOfLe h` for the resulting preimage.

end Semiring

section Ideal

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- If `H'` stabilizes an ideal, the quotient action on `B ^ H` fixes its contraction. -/
@[stacks 0BU6 "quotient action fixes a nested fixed-point contraction"]
theorem quotientAction_smul_under_of_le_stabilizer
    {H H' : Subgroup G} (h : H ≤ H') [Subgroup.Normal (H.subgroupOf H')]
    (m : Ideal B) (hfix : H' ≤ MulAction.stabilizer G m)
    (sigma : H' ⧸ H.subgroupOf H') :
    -- Local instance justification (defeq pin): the ideal action must use the canonical quotient
    -- action selected by `quotientAction h`.
    letI : MulSemiringAction (H' ⧸ H.subgroupOf H')
        (FixedPoints.subalgebra A B H) := quotientAction h
    sigma • m.under (FixedPoints.subalgebra A B H) =
      m.under (FixedPoints.subalgebra A B H) := sorry

-- Proof strategy: use quotient induction on `sigma`.  After ideal extensionality, rewrite the
-- quotient action on elements by `algebraMap_quotientAction_mk`; membership in the contraction is
-- preserved because the representative lies in `H'` and `hfix` says `H'` stabilizes `m`.

/-- If `H'` stabilizes an ideal, its contraction to `B ^ H` is stable under `H' / H`. -/
@[stacks 0BU6 "stability of a nested fixed-point contraction"]
theorem under_isStable_quotientAction_of_le_stabilizer
    {H H' : Subgroup G} (h : H ≤ H') [Subgroup.Normal (H.subgroupOf H')]
    (m : Ideal B) (hfix : H' ≤ MulAction.stabilizer G m) :
    -- Local instance justification (defeq pin): stability is stated for the canonical quotient
    -- action selected by `quotientAction h`.
    letI : MulSemiringAction (H' ⧸ H.subgroupOf H')
        (FixedPoints.subalgebra A B H) := quotientAction h
    (m.under (FixedPoints.subalgebra A B H)).IsStable
      (H' ⧸ H.subgroupOf H') := sorry

-- Proof strategy: unfold `Ideal.IsStable` and apply
-- `quotientAction_smul_under_of_le_stabilizer` to every quotient element.

end Ideal

section Domain

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
variable [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- For a finite group acting faithfully on a domain, `H' ⧸ H.subgroupOf H'` is the Galois
group of the fixed-subalgebra extension `B ^ H / B ^ H'`. -/
@[stacks 0BU6 "Galois quotient between nested fixed subalgebras"]
theorem quotientIsGaloisGroup {H H' : Subgroup G} (h : H ≤ H')
    [Subgroup.Normal (H.subgroupOf H')] :
    letI : Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
      subalgebraAlgebraOfLe h
    letI : MulSemiringAction (H' ⧸ H.subgroupOf H') (FixedPoints.subalgebra A B H) :=
      quotientAction h
    IsGaloisGroup (H' ⧸ H.subgroupOf H') (FixedPoints.subalgebra A B H')
      (FixedPoints.subalgebra A B H) := sorry

-- Proof strategy: combine `quotientIsInvariant` with Mathlib's quotient theorem for the finite
-- Galois action `subgroupOfIsGaloisGroup h`; use the representative formula to transport
-- faithfulness and the fixed-point condition to the named quotient action.

end Domain

end FixedPoints
