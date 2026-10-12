/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Regularity of an algebraic space at a point

An algebraic space is regular at a point when the local ring of every étale scheme chart
through that point is a regular local ring. Equivalently, this holds for some such chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space `X` is regular at a point `x` if `U.left.presheaf.stalk u` is a
regular local ring for every étale morphism `a : ofOver U ⟶ X` from a scheme over `S`
with `Points.mapOfOver a u = x`. -/
@[mk_iff]
class RegularAt {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) : Prop where
  /-- The stalk of any étale scheme chart through `x` is a regular local ring. -/
  of_etale {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x) : IsRegularLocalRing (U.left.presheaf.stalk u)

namespace RegularAt

/-- Regularity at a point implies that every étale scheme chart through that point has a
regular local stalk. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} [RegularAt X x]
    {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x) :
    IsRegularLocalRing (U.left.presheaf.stalk u) := sorry

/-- A single étale scheme chart with regular local stalk witnesses regularity at the image
point. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} {U : Over S}
    (a : ofOver U ⟶ X) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x)
    [IsRegularLocalRing (U.left.presheaf.stalk u)] :
    RegularAt X x := sorry

/-- Regularity at a point is equivalent to the existence of some étale scheme chart through
that point with regular local stalk. -/
theorem iff_exists {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    RegularAt X x ↔
      ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          Points.mapOfOver a u = x ∧
            IsRegularLocalRing (U.left.presheaf.stalk u) := sorry

end RegularAt

/-- A scheme over `S`, viewed as an algebraic space, is regular at a point whenever the
corresponding scheme stalk is a regular local ring. -/
instance instRegularAt_ofOver {S : Scheme.{u}} {T : Over S} {t : T.left}
    [IsRegularLocalRing (T.left.presheaf.stalk t)] :
    RegularAt (ofOver T) (ofOver.pointsEquiv T t) := sorry

/-- On a scheme over `S`, viewed as an algebraic space, regularity at a point is the usual
regularity of the scheme stalk. -/
theorem regularAt_ofOver_iff {S : Scheme.{u}} (T : Over S) (t : T.left) :
    RegularAt (ofOver T) (ofOver.pointsEquiv T t) ↔
      IsRegularLocalRing (T.left.presheaf.stalk t) := sorry

end AlgebraicGeometry.AlgebraicSpace
