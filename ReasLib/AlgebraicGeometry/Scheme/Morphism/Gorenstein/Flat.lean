/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.RingTheory.Gorenstein.FlatLocal

/-!
# Gorenstein morphisms from Gorenstein schemes

This file records Gorenstein consequences of flat morphisms whose source is
Gorenstein.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Gorenstein

/-- A flat morphism from a Gorenstein scheme to a locally Noetherian scheme is
Gorenstein. -/
instance of_flat_of_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Scheme.Gorenstein X] [IsLocallyNoetherian Y] [Flat f] :
    Gorenstein f := sorry

end Gorenstein

namespace Scheme.Gorenstein

/-- For a flat morphism from a Gorenstein scheme to a locally Noetherian scheme,
every target stalk at a point in the image is a Gorenstein local ring. -/
instance instTargetStalkOfFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Scheme.Gorenstein X] [IsLocallyNoetherian Y] [Flat f] (x : X) :
    IsGorensteinLocalRing (Y.presheaf.stalk (f x)) := sorry

end Scheme.Gorenstein
end AlgebraicGeometry
