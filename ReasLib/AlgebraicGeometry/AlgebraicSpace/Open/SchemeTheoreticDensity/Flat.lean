/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Flat inverse images of scheme-theoretically dense quasi-compact opens

The inverse image of a scheme-theoretically dense quasi-compact open immersion
of algebraic spaces along a flat morphism is again scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Scheme-theoretic dominance of a quasi-compact open immersion is preserved by
pullback along a flat morphism of algebraic spaces. -/
theorem IsSchemeTheoreticallyDominant.of_isPullback {S : Scheme.{u}}
    {X Y V P : AlgebraicSpace S} {f : X ⟶ Y} {ι : V ⟶ Y} {pX : P ⟶ X}
    {pV : P ⟶ V} (h : IsPullback pX pV f ι) [Flat f] [IsOpenImmersion ι]
    [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι] :
    IsSchemeTheoreticallyDominant pX :=
  sorry

/-- The inverse-image inclusion of a scheme-theoretically dominant quasi-compact
open immersion along a flat morphism of algebraic spaces is scheme-theoretically
dominant. -/
instance IsSchemeTheoreticallyDominant.openInverseImageι {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (ι : V ⟶ Y)
    [IsOpenImmersion ι] [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι] :
    IsSchemeTheoreticallyDominant (openInverseImageι f ι) :=
  IsSchemeTheoreticallyDominant.of_isPullback (openInverseImage_isPullback f ι)

end AlgebraicGeometry.AlgebraicSpace
