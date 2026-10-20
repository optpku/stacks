/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Reducedness of relative normalizations of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The relative normalization of an algebraic space in a reduced algebraic space along a
quasi-compact and quasi-separated morphism is reduced. -/
theorem isReduced_normalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [IsReduced X] :
    IsReduced (normalization f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
