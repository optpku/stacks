module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.NumericalType.PicardBounds

/- Proposition 55.7.4 (1): for a numerical type `T` of genus `g ≥ 2` and a
prime `ell > 768 * g`, the `ZMod ell`-dimension of `T.PicardGroup[ell]` is at
most `g`. -/
@[stacks 0C9X] #check (NumericalType.picardTorsionFinrank_le_genus :
    ∀ (g : ℤ), 2 ≤ g → ∀ (T : NumericalType), T.genus = g →
      ∀ (ell : ℕ), Fact ell.Prime → (768 : ℤ) * g < (ell : ℤ) →
      (@Module.finrank (ZMod ell)
          (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ)) _ _
          (AddSubgroup.torsionBy.zmodModule :
            Module (ZMod ell) (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ))) : ℤ) ≤
        g)

/- Proposition 55.7.4 (2): if `T` is minimal, the `ZMod ell`-dimension of
`T.PicardGroup[ell]` is at most the topological genus and the topological genus
is at most `g`. -/
@[stacks 0C9X] #check (NumericalType.picardTorsionFinrank_le_topologicalGenus :
    ∀ (g : ℤ), 2 ≤ g → ∀ (T : NumericalType), T.genus = g →
      ∀ (ell : ℕ), Fact ell.Prime → (768 : ℤ) * g < (ell : ℤ) →
      T.IsMinimal →
      (@Module.finrank (ZMod ell)
          (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ)) _ _
          (AddSubgroup.torsionBy.zmodModule :
            Module (ZMod ell) (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ))) : ℤ) ≤
          (T.topologicalGenus : ℤ) ∧
        (T.topologicalGenus : ℤ) ≤ g)
