/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion

/-- A separated, locally finite-type, flat morphism of algebraic spaces is an open
immersion if its restriction to a quasi-compact scheme-theoretically dense open
subspace of the target is an isomorphism. -/
theorem of_isIso_restrict_of_flat {S : Scheme.{u}} {X Y V : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] [Flat f] (ι : V ⟶ Y)
    [IsOpenImmersion ι] [QuasiCompact ι] [IsSchemeTheoreticallyDense ι]
    [IsIso (openInverseImageTo f ι)] :
    IsOpenImmersion f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion
