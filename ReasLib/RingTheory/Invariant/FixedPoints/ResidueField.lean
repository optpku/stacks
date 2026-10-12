/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints.Subalgebra
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Residue fields of nested fixed subalgebras

This leaf owns the residue-field algebra induced by a subgroup inclusion.  The construction is
named data rather than a global instance because one residue-field carrier can occur in several
different towers.  A companion theorem records coherence along a chain of subgroup inclusions.
@stack 0BU6
-/

universe u v w

namespace FixedPoints.ResidueField

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The canonical residue-field algebra induced contravariantly by `H ≤ H'`. -/
@[implicit_reducible, stacks 0BU6 "residue algebra along a fixed-subalgebra inclusion"]
noncomputable def algebraOfLe {H H' : Subgroup G} (h : H ≤ H')
    (m : Ideal B) [m.IsPrime] :
    Algebra
      (m.under (FixedPoints.subalgebra A B H')).ResidueField
      (m.under (FixedPoints.subalgebra A B H)).ResidueField :=
  -- Local instance justification (defeq pin): the residue map must use the canonical inclusion
  -- selected by `subalgebraAlgebraOfLe h`.
  letI : Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
    FixedPoints.subalgebraAlgebraOfLe h
  -- Local instance justification (defeq pin): this is the contraction pair determined by `h` and
  -- `m`, so `algebraOfLiesOver` must consume exactly its canonical lying-over proof.
  letI : (m.under (FixedPoints.subalgebra A B H)).LiesOver
      (m.under (FixedPoints.subalgebra A B H')) :=
    FixedPoints.under_liesOver_under_of_le h m
  Ideal.ResidueField.algebraOfLiesOver
    (m.under (FixedPoints.subalgebra A B H'))
    (m.under (FixedPoints.subalgebra A B H))

/-- Residue-field algebras attached to `H₁ ≤ H₂ ≤ H₃` form the corresponding scalar tower. -/
@[stacks 0BU6 "residue-field scalar tower for nested fixed subalgebras"]
theorem isScalarTower_of_le_of_le
    {H₁ H₂ H₃ : Subgroup G} (h₁₂ : H₁ ≤ H₂) (h₂₃ : H₂ ≤ H₃)
    (m : Ideal B) [m.IsPrime] :
    -- Local instance justification (defeq pin): all three residue maps must be the named maps
    -- selected by `algebraOfLe` for this subgroup chain.
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B H₃)).ResidueField
        (m.under (FixedPoints.subalgebra A B H₂)).ResidueField :=
      algebraOfLe h₂₃ m
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B H₂)).ResidueField
        (m.under (FixedPoints.subalgebra A B H₁)).ResidueField :=
      algebraOfLe h₁₂ m
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B H₃)).ResidueField
        (m.under (FixedPoints.subalgebra A B H₁)).ResidueField :=
      algebraOfLe (h₁₂.trans h₂₃) m
    IsScalarTower
      (m.under (FixedPoints.subalgebra A B H₃)).ResidueField
      (m.under (FixedPoints.subalgebra A B H₂)).ResidueField
      (m.under (FixedPoints.subalgebra A B H₁)).ResidueField := sorry

-- Proof strategy: rewrite each named residue algebra map with
-- `Ideal.ResidueField.algebraMap_algebraOfLiesOver`.  Apply `Ideal.ResidueField.map_comp` to the
-- three canonical fixed-subalgebra inclusions, using
-- `subalgebra_isScalarTower_of_le_of_le` to identify their composite, then conclude with
-- `IsScalarTower.of_algebraMap_eq'`.

end FixedPoints.ResidueField
