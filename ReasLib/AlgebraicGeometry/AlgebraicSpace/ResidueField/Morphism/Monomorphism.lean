/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism

/-!
# Residue fields under monomorphisms of algebraic spaces

A monomorphism between decent algebraic spaces induces isomorphisms on residue fields.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The residue-field map induced by a monomorphism of decent algebraic spaces is
an isomorphism. -/
instance isIso_residueFieldMap_of_mono {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X] (i : Y ⟶ X) [Mono i] (y : Points Y) :
    IsIso (residueFieldMap i y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
