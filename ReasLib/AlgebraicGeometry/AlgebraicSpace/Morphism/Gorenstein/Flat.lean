/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local

/-!
# Flat morphisms from Gorenstein algebraic spaces

A flat morphism of locally Noetherian algebraic spaces with Gorenstein source is
Gorenstein, and the étale local ring of the target at the image of every
geometric point of the source is a Gorenstein local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Gorenstein

/-- A flat morphism of locally Noetherian algebraic spaces over a scheme with
Gorenstein source is Gorenstein. -/
instance of_flat_of_source {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [IsGorenstein X] :
    Gorenstein f :=
  sorry

end Gorenstein

namespace IsGorenstein

/-- For a flat morphism of locally Noetherian algebraic spaces over a scheme
with Gorenstein source, the target étale local ring at the image of every source
geometric point is Gorenstein. -/
instance instTargetEtaleLocalRingOfFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [IsGorenstein X] (xbar : GeometricPoint X) :
    IsGorensteinLocalRing (etaleLocalRing Y (xbar.map f)) :=
  sorry

end IsGorenstein

end AlgebraicGeometry.AlgebraicSpace
