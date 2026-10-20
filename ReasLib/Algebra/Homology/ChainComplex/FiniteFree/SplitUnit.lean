module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Coordinates
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.IdentityDisk

@[expose] public section

/-!
# Splitting a unit entry from a finite free complex

@stack 00MT

This leaf owns the decomposition theorem; coordinate changes, rank profiles,
and the coordinate identity disk remain in their finer-grained owner leaves.
-/

open CategoryTheory CategoryTheory.Limits ChainComplex

noncomputable section

universe u

namespace FiniteFreeComplex

/-- Lemma 10.102.2 (00MT): a unit coefficient in a displayed differential
splits off the identity disk in the two adjacent degrees. -/
@[stacks 00MT]
theorem exists_iso_biprod_identityDisk_of_isUnit_diffEntry
    {R : Type u} [Ring R] {e : ℕ}
    (C : _root_.FiniteFreeComplex R e) (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
        IsUnit (C.diffEntry i a b)) :
    ∃ C' : _root_.FiniteFreeComplex R e,
      C'.rank = splitRank C.rank i ∧
      Nonempty (C.toChainComplex ≅ biprod C'.toChainComplex (identityDiskComplex i)) := sorry

end FiniteFreeComplex
