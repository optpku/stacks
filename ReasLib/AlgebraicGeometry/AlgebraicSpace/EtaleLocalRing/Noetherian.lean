/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Étale local rings of Noetherian algebraic spaces

The étale-site stalk of a locally Noetherian algebraic space at a geometric point is a
Noetherian local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale local ring of a locally Noetherian algebraic space at a geometric point is a
Noetherian ring. -/
theorem etaleLocalRing.instIsNoetherianRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (xbar : GeometricPoint X) :
    IsNoetherianRing (etaleLocalRing X xbar) :=
  sorry

/-- The étale local ring of a locally Noetherian algebraic space at a geometric point is a
local ring. -/
theorem etaleLocalRing.instIsLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (xbar : GeometricPoint X) :
    IsLocalRing (etaleLocalRing X xbar) :=
  sorry

/-- If `X` is a Noetherian algebraic space over a scheme `S` and `xbar` is a geometric
point of `X`, then `etaleLocalRing X xbar` is a Noetherian local ring. -/
theorem etaleLocalRing.isNoetherianLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsNoetherian X] (xbar : GeometricPoint X) :
    IsNoetherianRing (etaleLocalRing X xbar) ∧ IsLocalRing (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
