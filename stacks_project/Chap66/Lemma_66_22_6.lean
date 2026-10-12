/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Remark_66_7_6_LocalRing
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Reducedness of étale local rings

The local ring of an algebraic space at a point is reduced if and only if the étale-site
stalk at some, equivalently any, geometric point over that point is reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.22.6: let `S` be a scheme, let `X` be an algebraic space over `S`, and let `x`
be a point of `|X|`. The following are equivalent: the local ring of `X` at `x` is reduced
in the sense of Remark 66.7.6; the étale-site stalk `𝒪_{X, xbar}` is reduced for some
geometric point `xbar` lying over `x`; and `𝒪_{X, xbar}` is reduced for every geometric
point `xbar` lying over `x`. -/
@[stacks 0E01]
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
