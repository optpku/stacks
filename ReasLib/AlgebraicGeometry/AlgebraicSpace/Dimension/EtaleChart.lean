module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing.Examples
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Krull dimension on étale charts of algebraic spaces

The stalk dimension on an étale scheme chart through a point is independent of the chart
and agrees with the ordinary stalk dimension for a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Some étale scheme chart through a point has stalk of Krull dimension `d` if and only if
every étale scheme chart through that point has stalk of Krull dimension `d`. -/
@[stacks 0BAM]
theorem localRingHas_ringKrullDim_iff_forallEtaleAt {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) (d : WithBot ℕ∞) :
    localRingHas (fun R ↦ ringKrullDim R = d) X x ↔
      forallEtaleAt (GermProperty.ofLocalRing fun R ↦ ringKrullDim R = d) X x :=
  sorry

/-- For a scheme over the base, the chart condition for stalk dimension `d` is equivalent
to its ordinary stalk having Krull dimension `d`. -/
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
