module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory AddSubgroup
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsThickening

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i]

/-- If an integer is invertible in the global sections of a scheme, pullback along a
thickening bijects the corresponding torsion subgroups of the Picard groups. -/
theorem picardPullback_bijOn_torsionBy (n : ℤ)
    (h_unit : IsUnit (n : Γ(X, ⊤))) :
    Set.BijOn (Scheme.Hom.picardPullback i) X'.PicardGroup[n] X.PicardGroup[n] := sorry

end AlgebraicGeometry.IsThickening
