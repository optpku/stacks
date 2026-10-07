module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.AlgebraicGeometry.NumericalType.InvariantBounds
public import ReasLib.AlgebraicGeometry.NumericalType.Picard

@[expose] public section

namespace NumericalType

/-- For a numerical type of genus `g ≥ 2` and a prime `ell > 768 * g`, the
`ZMod ell`-dimension of the `ell`-torsion in its Picard group is at most `g`. -/
public theorem picardTorsionFinrank_le_genus
    (g : ℤ) (hg : 2 ≤ g) (T : NumericalType) (hgenus : T.genus = g)
    (ell : ℕ) [Fact ell.Prime] (h_large : (768 : ℤ) * g < (ell : ℤ)) :
    (@Module.finrank (ZMod ell)
        (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ)) _ _
        (AddSubgroup.torsionBy.zmodModule :
          Module (ZMod ell) (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ))) : ℤ) ≤
      g := sorry

/-- If a numerical type is minimal, its `ell`-torsion Picard-group dimension
is at most its topological genus, which is at most its genus. -/
public theorem picardTorsionFinrank_le_topologicalGenus
    (g : ℤ) (hg : 2 ≤ g) (T : NumericalType) (hgenus : T.genus = g)
    (ell : ℕ) [Fact ell.Prime] (h_large : (768 : ℤ) * g < (ell : ℤ))
    (hminimal : T.IsMinimal) :
    (@Module.finrank (ZMod ell)
        (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ)) _ _
        (AddSubgroup.torsionBy.zmodModule :
          Module (ZMod ell) (AddSubgroup.torsionBy T.PicardGroup (ell : ℤ))) : ℤ) ≤
        (T.topologicalGenus : ℤ) ∧
      (T.topologicalGenus : ℤ) ≤ g := sorry

end NumericalType
