module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Composition of admissible blowups

Successive blowups admissible over a quasi-compact open subspace of a
quasi-compact, absolutely quasi-separated algebraic space have admissible composite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Over a quasi-compact open subspace of a quasi-compact, absolutely
quasi-separated algebraic space, the composite of an admissible blowup and a
blowup admissible over the inverse-image open subspace is admissible. -/
@[stacks 086C]
theorem IsAdmissibleBlowup.comp {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b)
    (b' : X'' ⟶ X') (hb' : IsAdmissibleBlowup (U.inverseImage b) b') :
    IsAdmissibleBlowup U (b' ≫ b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
