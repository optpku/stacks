/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-!
# Locality of inverse-image structure maps of algebraic spaces

A morphism of algebraic spaces induces a local morphism of small étale ringed topoi.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Sheaf.LocalHom

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The canonical inverse-image structure-sheaf map of a morphism of algebraic spaces
is local. -/
instance commInverseImageStructureSheafMap_isLocal (f : X ⟶ Y) :
    IsLocal (commInverseImageStructureSheafMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
