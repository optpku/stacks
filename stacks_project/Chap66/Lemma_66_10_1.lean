module

public import Mathlib.RingTheory.KrullDimension.Basic
public import stacks_project.Chap66.Remark_66_7_6_LocalRing
public import stacks_project.Chap66.Remark_66_7_6_Instances

/-!
# Well-definedness of the Krull dimension of local rings of algebraic spaces

The condition that an étale scheme chart through a point of an algebraic space has stalk of
Krull dimension `d` is independent of the choice of chart, and recovers the usual stalk
dimension when the algebraic space is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.10.1 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, let `x` be
a point of `X`, and let `d : WithBot ℕ∞`. Then some étale scheme chart through `x` has stalk of
Krull dimension `d` if and only if every étale scheme chart through `x` has stalk of Krull
dimension `d`. -/
@[stacks 0BAM]
theorem localRingHas_ringKrullDim_iff_forallEtaleAt {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) (d : WithBot ℕ∞) :
    localRingHas (fun R ↦ ringKrullDim R = d) X x ↔
      forallEtaleAt (GermProperty.ofLocalRing fun R ↦ ringKrullDim R = d) X x :=
  sorry

/-- Lemma 66.10.1 (2): if `X` is representable by a scheme `T` over `S`, then the local ring of
`X` at the image of `t` has Krull dimension `d` if and only if
`ringKrullDim (T.left.presheaf.stalk t) = d`. -/
@[stacks 0BAM]
theorem localRingHas_ringKrullDim_ofOver {S : Scheme.{u}} (T : Over S) (t : T.left)
    (d : WithBot ℕ∞) :
    localRingHas (fun R ↦ ringKrullDim R = d) (ofOver T) (ofOver.pointsEquiv T t) ↔
      ringKrullDim (T.left.presheaf.stalk t) = d :=
  sorry

/-- The Krull dimension of the stalk of an étale scheme chart through a common point of an
algebraic space is independent of the choice of chart. -/
theorem ringKrullDim_stalk_eq_of_etaleAt {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ X)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (u : U.left) (v : V.left) (h : Points.mapOfOver a u = Points.mapOfOver b v) :
    ringKrullDim (U.left.presheaf.stalk u) = ringKrullDim (V.left.presheaf.stalk v) :=
  sorry

/-- The value `d` such that the local ring of `X` at `x` has Krull dimension `d` is unique. -/
theorem eq_of_localRingHas_ringKrullDim {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    {d d' : WithBot ℕ∞} (hd : localRingHas (fun R ↦ ringKrullDim R = d) X x)
    (hd' : localRingHas (fun R ↦ ringKrullDim R = d') X x) : d = d' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
