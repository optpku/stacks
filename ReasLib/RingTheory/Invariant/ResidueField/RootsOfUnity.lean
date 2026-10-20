module

public import ReasLib.RingTheory.Invariant.ResidueField
public import ReasLib.RingTheory.RootsOfUnity.Action
public import Mathlib.RingTheory.Ideal.Pointwise

@[expose] public section

/-!
# Roots of unity in invariant residue fields

This file derives the action on roots of unity from the canonical action of a decomposition
group on the corresponding residue field.
@stack 0BU5
-/

universe u v w

namespace Ideal.ResidueField.Invariant

open scoped Pointwise

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]

/-- The decomposition group at `q` acts on the `n`th roots of unity in `q.ResidueField`.

The residue-field algebra is scoped because it is determined by the chosen lying-over pair
`(p, q)` and therefore should not be installed globally. -/
@[stacks 0BU5 "decomposition-group action on residue roots of unity"]
noncomputable def rootsOfUnityHom
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (n : ℕ) :
    MulAction.stabilizer G q →* MulAut (rootsOfUnity n q.ResidueField) :=
  -- Local instance justification (defeq pin): restrict the canonical residue action using the lying-over residue algebra.
  letI : Algebra p.ResidueField q.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p q
  (MulAut.restrictRootsOfUnityHom n).comp
    ((MulDistribMulAction.toMulAut
      Gal(q.ResidueField / p.ResidueField) q.ResidueField).comp
        (stabilizerHom G p q))

/-- The action on residue roots of unity is the restriction of the residue-field action. -/
@[simp, stacks 0BU5 "decomposition-group action on residue roots of unity formula"]
theorem rootsOfUnityHom_apply
    (G : Type w) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (n : ℕ) (tau : MulAction.stabilizer G q) :
    -- Local instance justification (defeq pin): compare root actions under the same canonical residue algebra.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    rootsOfUnityHom G p q n tau =
      (stabilizerHom G p q tau).toMulEquiv.restrictRootsOfUnity n := sorry

-- Proof strategy: unfold `rootsOfUnityHom`, reduce evaluation of the two composed monoid
-- homomorphisms, and apply extensionality for `MulAut`; the residue-field action is exactly
-- `Ideal.ResidueField.Invariant.stabilizerHom`, and restriction to roots of unity is definitional.

end Ideal.ResidueField.Invariant
