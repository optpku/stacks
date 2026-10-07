module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_25_2_RegularAt
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Regularity of étale local rings

An algebraic space is regular at a point if and only if the étale-site stalk at some,
equivalently any, geometric point over that point is a regular local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.25.3: let `S` be a scheme, let `X` be an algebraic space over `S`, and let `x`
be a point of `|X|`. The following are equivalent: `X` is regular at `x`; the étale local
ring `𝒪_{X, xbar}` is a regular local ring for some geometric point `xbar` lying over `x`;
and `𝒪_{X, xbar}` is a regular local ring for every geometric point `xbar` lying over `x`. -/
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
