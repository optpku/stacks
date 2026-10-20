/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal.Complement

/-!
# Complements of locally principal closed subspaces

The open complement of a locally principal closed subspace of an algebraic space
maps affinely to the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal

/-- The inclusion of the open complement of a locally principal closed subspace
of an algebraic space is an affine morphism. -/
instance affine_closedImmersionComplementι {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsLocallyPrincipal i] :
    Affine (closedImmersionComplementι i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal
