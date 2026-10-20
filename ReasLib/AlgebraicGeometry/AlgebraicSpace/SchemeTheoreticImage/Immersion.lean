/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- An immersion of algebraic spaces that is quasi-compact or has reduced source
maps to any scheme-theoretic image as an open immersion with scheme-theoretically
dense and topologically dense image. -/
theorem isOpenImmersion_and_dense_toImage_of_quasiCompact_or_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsSchemeTheoreticImage f toImage ι]
    (hqc_or_red : QuasiCompact f ∨ IsReduced X) :
    IsOpenImmersion toImage ∧ Open.IsSchemeTheoreticallyDense toImage ∧ Dominant toImage :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
