module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Affineness of relative normalization

The relative normalization of a quasi-compact quasi-separated morphism into an
affine algebraic space is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Hom

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative normalization of a quasi-compact quasi-separated morphism into
an affine algebraic space is affine. -/
instance instIsAffine_normalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [IsAffine Y] :
    IsAffine (normalization f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
