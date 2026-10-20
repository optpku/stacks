/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Good
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-!
# Residue fields along open scheme subspaces

The inclusion of an open scheme subspace of a good algebraic space induces an
isomorphism on residue fields at every point of that subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue-field map of the inclusion of an open scheme subspace is an
isomorphism when the ambient algebraic space is quasi-separated and locally of
finite type over a quasi-separated algebraic space. -/
theorem isIso_residueFieldHom_of_isScheme_openSubspace {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] [IsDecent X]
    (U : OpenSubspace X) [IsScheme U.X] [IsDecent U.X] (y : Points U.X) :
    IsIso (Hom.residueFieldMap U.ι y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
