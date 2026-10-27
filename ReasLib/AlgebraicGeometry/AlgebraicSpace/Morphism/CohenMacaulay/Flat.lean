/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Flat morphisms from Cohen–Macaulay algebraic spaces

A flat morphism of locally Noetherian algebraic spaces with Cohen–Macaulay
source is Cohen–Macaulay, and the étale local ring of the target at the image
of every geometric point of the source is Cohen–Macaulay.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CohenMacaulay

/-- A flat morphism of locally Noetherian algebraic spaces over a scheme with
Cohen–Macaulay source is Cohen–Macaulay. -/
@[stacks 0E0Y]
theorem of_flat_of_source {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (hX : hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u}) X) :
    CohenMacaulay f :=
  sorry

end CohenMacaulay

namespace etaleLocalRing

/-- For a flat morphism of locally Noetherian algebraic spaces over a scheme
with Cohen–Macaulay source, the target étale local ring at the image of every
source geometric point is Cohen–Macaulay. -/
@[stacks 0E0Y]
theorem cohenMacaulayRing_of_flat_of_source {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (hX : hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u}) X)
    (xbar : GeometricPoint X) :
    CohenMacaulayRing (etaleLocalRing Y (xbar.map f)) :=
  sorry

end etaleLocalRing

end AlgebraicGeometry.AlgebraicSpace
