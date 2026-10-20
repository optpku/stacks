/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.ResiduePoint
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Splitting

/-!
# Stabilizer-support residue-field points of the finite-part localization

A scheme point `u` of the object scheme of a groupoid scheme determines the
stabilizer-support open `Z_u` in the source fibre over `Spec(κ(u))` and the
classifying morphism of the pair `(u, Z_u)` into the finite-part object space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The points of the residue source fibre mapping into the stabilizer fibre form
an open subset under the splitting hypotheses. -/
private theorem stabilizerOpen_isOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)] :
    IsOpen
      {z |
        Points.map
            (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z ∈
          GroupoidAlgebraicSpace.stabilizerFiberPoints
            (GroupoidAlgebraicSpace.ofScheme G) (ofOver.pointsEquiv G.U u)} :=
  sorry

/-- The support `Z_u ⊂ |Spec(κ(u)) ×_U R|` of points mapping into the stabilizer
fibre over `u`. -/
def stabilizerOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [Fact (SplittingHypotheses G u)] :
    Opens
      (Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) where
  carrier :=
    {z |
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z ∈
        GroupoidAlgebraicSpace.stabilizerFiberPoints
          (GroupoidAlgebraicSpace.ofScheme G) (ofOver.pointsEquiv G.U u)}
  is_open' := by exact stabilizerOpen_isOpen G u

/-- Membership in `stabilizerOpen G u` is equivalent to landing in the stabilizer
fibre over `u`. -/
theorem mem_stabilizerOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [Fact (SplittingHypotheses G u)]
    (z :
      Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) :
    z ∈ stabilizerOpen G u ↔
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z ∈
        GroupoidAlgebraicSpace.stabilizerFiberPoints
          (GroupoidAlgebraicSpace.ofScheme G) (ofOver.pointsEquiv G.U u) :=
  Iff.rfl

/-- The stabilizer-support open in the residue source fibre is finite over the
residue field under the splitting hypotheses. -/
private theorem stabilizerWithSection_isFinite {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)] :
    AlgebraicSpace.IsFinite ((OpenSubspace.fromOpens (stabilizerOpen G u)).ι ≫
      pullback.fst (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) :=
  sorry

/-- The unit section over the residue point lands in the stabilizer-support open. -/
private theorem stabilizerWithSection_contains_unit {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)] :
    Set.range (Points.map (FinitePart.unitSection (residueMap G u)
      (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G)))) ⊆
      stabilizerOpen G u :=
  sorry

/-- The pair `(u, Z_u)` as a `Spec(κ(u))`-point of `(R_s / U, e)_fin`. -/
def stabilizerWithSection {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [Fact (SplittingHypotheses G u)] :
    FinitePart.WithSection.Point (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G))
      (residueOver G u) where
  a := residueMap G u
  Z := stabilizerOpen G u
  isFinite := by exact stabilizerWithSection_isFinite G u
  contains_unit := by exact stabilizerWithSection_contains_unit G u

/-- The object map of `stabilizerWithSection G u` is `residueMap G u`. -/
theorem stabilizerWithSection_a {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)] :
    (stabilizerWithSection G u).a = residueMap G u :=
  rfl

/-- The morphism `u' : Spec(κ(u)) ⟶ U'` classifying the pair `(u, Z_u)`. -/
def splittingHom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [Fact (SplittingHypotheses G u)]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    ofOver (residueOver G u) ⟶
      (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  GroupoidAlgebraicSpace.withSectionHom (GroupoidAlgebraicSpace.ofScheme G)
    (stabilizerWithSection G u)

/-- The classifying morphism `u'` lies over `u : Spec(κ(u)) ⟶ U`. -/
theorem splittingHom_liesOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    splittingHom G u ≫
        GroupoidAlgebraicSpace.finitePartToU (GroupoidAlgebraicSpace.ofScheme G) =
      residueMap G u := by
  exact (GroupoidAlgebraicSpace.withSectionHom_toU
    (GroupoidAlgebraicSpace.ofScheme G) (stabilizerWithSection G u)).trans
      (stabilizerWithSection_a G u)

/-- The point of `|U'|` determined by the residue-field morphism `u'`. -/
def splittingResiduePoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    Points (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  residueFieldPoint G u (splittingHom G u)

/-- `splittingResiduePoint` is the residue-field point of `splittingHom`. -/
theorem splittingResiduePoint_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [Fact (SplittingHypotheses G u)]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    splittingResiduePoint G u = residueFieldPoint G u (splittingHom G u) :=
  rfl

end AlgebraicGeometry.GroupoidScheme
