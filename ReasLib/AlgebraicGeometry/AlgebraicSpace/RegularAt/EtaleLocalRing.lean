module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Regularity of étale local rings

An algebraic space is regular at a point if and only if the étale-site stalk at some,
equivalently any, geometric point over that point is a regular local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space `X` and a point `x`, the following are equivalent: `X` is
regular at `x`; the étale local ring at some geometric point over `x` is regular;
and the étale local ring at every geometric point over `x` is regular. -/
@[stacks 0AHA]
theorem regularAt_etaleLocalRing_tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    List.TFAE
      [RegularAt X x,
        ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ IsRegularLocalRing (etaleLocalRing X xbar),
        ∀ xbar : GeometricPoint X, xbar.liesOver x → IsRegularLocalRing (etaleLocalRing X xbar)] :=
  sorry

/-- `X` is regular at `x` if and only if the étale local ring `𝒪_{X, xbar}` is a regular
local ring for some geometric point `xbar` lying over `x`. -/
theorem regularAt_iff_exists_etaleLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    RegularAt X x ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ IsRegularLocalRing (etaleLocalRing X xbar) :=
  sorry

/-- `X` is regular at `x` if and only if the étale local ring `𝒪_{X, xbar}` is a regular
local ring for every geometric point `xbar` lying over `x`. -/
theorem regularAt_iff_forall_etaleLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    RegularAt X x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → IsRegularLocalRing (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
