module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Reducedness of étale local rings

The local ring of an algebraic space at a point is reduced if and only if the étale-site
stalk at some, equivalently any, geometric point over that point is reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme, let `X` be an algebraic space over `S`, and let `x` be a point of
`|X|`. The following are equivalent: the local ring of `X` at `x` is reduced in the sense of
`localRingHas`; the étale-site stalk `𝒪_{X, xbar}` is reduced for some geometric point
`xbar` lying over `x`; and the étale-site stalk is reduced for every geometric point lying
over `x`. -/
theorem etaleLocalRing_isReduced_tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    List.TFAE
      [localRingHas (fun R ↦ _root_.IsReduced R) X x,
        ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ _root_.IsReduced (etaleLocalRing X xbar),
        ∀ xbar : GeometricPoint X, xbar.liesOver x → _root_.IsReduced (etaleLocalRing X xbar)] :=
  sorry

/-- The local ring of `X` at `x` is reduced if and only if the étale-site stalk
`𝒪_{X, xbar}` is reduced for some geometric point `xbar` lying over `x`. -/
theorem localRingHas_isReduced_iff_exists_etaleLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} (x : Points X) :
    localRingHas (fun R ↦ _root_.IsReduced R) X x ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ _root_.IsReduced (etaleLocalRing X xbar) :=
  sorry

/-- The local ring of `X` at `x` is reduced if and only if the étale-site stalk
`𝒪_{X, xbar}` is reduced for every geometric point `xbar` lying over `x`. -/
theorem localRingHas_isReduced_iff_forall_etaleLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} (x : Points X) :
    localRingHas (fun R ↦ _root_.IsReduced R) X x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → _root_.IsReduced (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

