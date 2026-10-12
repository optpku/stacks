/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap79.Definition_79_15_1_Splitting
public import stacks_project.Chap79.Lemma_79_14_1_Groupoid
public import stacks_project.Chap79.Lemma_79_14_1_Section
public import stacks_project.Chap79.Lemma_79_15_5_Existence_of_strong_splitting_ResiduePoint
public import stacks_project.Chap79.Situation_79_15_4_Quasi_splitting_Setup

/-!
# Identity-support residue-field points of the finite-part localization

A scheme point `u` of the object scheme of a groupoid scheme determines the
identity-support open `Z_u` in the source fibre over `Spec(κ(u))` and the
classifying morphism of the pair `(u, Z_u)` into the finite-part object space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The support `Z_u ⊂ |Spec(κ(u)) ×_U R|` of points mapping to the identity
arrow `e(u)`. -/
def identityOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    Opens
      (Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) where
  carrier :=
    {z |
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z =
        Points.map (GroupoidAlgebraicSpace.ofScheme G).e.left (ofOver.pointsEquiv G.U u)}
  is_open' := sorry

/-- Membership in `identityOpen G u` is equivalent to landing at the identity
arrow `e(u)`. -/
theorem mem_identityOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    (z :
      Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) :
    z ∈ identityOpen G u ↔
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z =
        Points.map (GroupoidAlgebraicSpace.ofScheme G).e.left (ofOver.pointsEquiv G.U u) :=
  sorry

/-- The pair `(u, Z_u)` as a `Spec(κ(u))`-point of `(R_s / U, e)_fin`. -/
def identityWithSection {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u] :
    FinitePart.WithSection.Point (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G))
      (residueOver G u) where
  a := residueMap G u
  Z := identityOpen G u
  isFinite := sorry
  contains_unit := sorry

/-- The object map of `identityWithSection G u` is `residueMap G u`. -/
theorem identityWithSection_a {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u] :
    (identityWithSection G u).a = residueMap G u :=
  rfl

/-- The morphism `u' : Spec(κ(u)) ⟶ U'` classifying the pair `(u, Z_u)`. -/
def quasiSplittingHom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    ofOver (residueOver G u) ⟶
      (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  GroupoidAlgebraicSpace.withSectionHom (GroupoidAlgebraicSpace.ofScheme G)
    (identityWithSection G u)

/-- The classifying morphism `u'` lies over `u : Spec(κ(u)) ⟶ U`. -/
theorem quasiSplittingHom_liesOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    quasiSplittingHom G u ≫
        GroupoidAlgebraicSpace.finitePartToU (GroupoidAlgebraicSpace.ofScheme G) =
      residueMap G u :=
  sorry

/-- The point of `|U'|` determined by the residue-field morphism `u'`. -/
def quasiSplittingResiduePoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    Points (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  residueFieldPoint G u (quasiSplittingHom G u)

/-- `quasiSplittingResiduePoint` is the residue-field point of
`quasiSplittingHom`. -/
theorem quasiSplittingResiduePoint_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    quasiSplittingResiduePoint G u =
      residueFieldPoint G u (quasiSplittingHom G u) :=
  rfl

end AlgebraicGeometry.GroupoidScheme
