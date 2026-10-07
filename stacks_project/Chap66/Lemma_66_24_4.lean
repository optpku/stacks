module

public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_24_1_Noetherian

/-!
# Étale local rings of Noetherian algebraic spaces

The étale-site stalk of a locally Noetherian algebraic space at a geometric point is a
Noetherian local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.24.4: if `X` is a locally Noetherian algebraic space over a scheme `S` and
`xbar` is a geometric point of `X`, then the étale local ring `etaleLocalRing X xbar` is a
Noetherian ring. -/
@[stacks 08AH]
instance etaleLocalRing.instIsNoetherianRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (xbar : GeometricPoint X) :
    IsNoetherianRing (etaleLocalRing X xbar) :=
  sorry

/-- The étale local ring of a locally Noetherian algebraic space at a geometric point is a
local ring. -/
instance etaleLocalRing.instIsLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
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
