/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.FinitePart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Splitting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.GroupoidScheme.StrongSplitting

/-!
# Residue-field points of the finite-part localization

A scheme point `u` of the object scheme of a groupoid scheme determines the
residue-field object `Spec(κ(u))` over `S`, the equalizer open `Z_u` in the
source fibre, and the classifying morphism of the pair `(u, Z_u)` into the
finite-part object space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The residue-field scheme `Spec(κ(u))` of an object point, as a scheme over `S`. -/
def residueOver {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) : Over S :=
  Over.mk (G.U.left.fromSpecResidueField u ≫ G.U.hom)

/-- The structure morphism of `residueOver G u` is `Spec(κ(u)) ⟶ S`. -/
theorem residueOver_hom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    (residueOver G u).hom = G.U.left.fromSpecResidueField u ≫ G.U.hom :=
  rfl

/-- Compatibility of `fromSpecResidueField u` with the structure morphisms over `S`. -/
private theorem residueMap_w {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    G.U.left.fromSpecResidueField u ≫ G.U.hom = (residueOver G u).hom :=
  rfl

/-- The morphism `u : Spec(κ(u)) ⟶ U` as a morphism of algebraic spaces over `S`. -/
def residueMap {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    ofOver (residueOver G u) ⟶ ofOver G.U :=
  ofOverMap (Over.homMk (G.U.left.fromSpecResidueField u) (by exact residueMap_w G u))

/-- The points of the residue source fibre mapping to loop arrows form an open subset. -/
private theorem equalizerOpen_isOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    IsOpen
    {z |
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z ∈
        GroupoidAlgebraicSpace.sourceTargetFiber (GroupoidAlgebraicSpace.ofScheme G)
          (ofOver.pointsEquiv G.U u)} :=
  sorry

/-- The open `Z_u ⊂ |Spec(κ(u)) ×_U R|` of points mapping into the source-target
fibre at `u`. -/
def equalizerOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [StrongSplitting G u] :
    Opens
      (Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) where
  carrier :=
    {z |
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z ∈
        GroupoidAlgebraicSpace.sourceTargetFiber (GroupoidAlgebraicSpace.ofScheme G)
          (ofOver.pointsEquiv G.U u)}
  is_open' := by exact equalizerOpen_isOpen G u

/-- Membership in `equalizerOpen G u` is equivalent to landing in the source-target
fibre at `u`. -/
theorem mem_equalizerOpen {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [StrongSplitting G u]
    (z :
      Points
        (pullback (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left)) :
    z ∈ equalizerOpen G u ↔
      Points.map
          (pullback.snd (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) z ∈
        GroupoidAlgebraicSpace.sourceTargetFiber (GroupoidAlgebraicSpace.ofScheme G)
          (ofOver.pointsEquiv G.U u) :=
  Iff.rfl

/-- The open of loop arrows in the residue source fibre is finite over the residue field. -/
private theorem equalizerWithSection_isFinite {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    AlgebraicSpace.IsFinite ((OpenSubspace.fromOpens (equalizerOpen G u)).ι ≫
      pullback.fst (residueMap G u) (GroupoidAlgebraicSpace.ofScheme G).s.left) :=
  sorry

/-- The unit section over the residue point lands in the open of loop arrows. -/
private theorem equalizerWithSection_contains_unit {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    Set.range (Points.map (FinitePart.unitSection (residueMap G u)
      (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G)))) ⊆
      equalizerOpen G u :=
  sorry

/-- The pair `(u, Z_u)` as a `Spec(κ(u))`-point of `(R_s / U, e)_fin`. -/
def equalizerWithSection {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [StrongSplitting G u] :
    FinitePart.WithSection.Point (GroupoidAlgebraicSpace.ofScheme G).s.left
      (GroupoidAlgebraicSpace.ofScheme G).e.left
      (GroupoidAlgebraicSpace.unit_source_left (GroupoidAlgebraicSpace.ofScheme G))
      (residueOver G u) where
  a := residueMap G u
  Z := equalizerOpen G u
  isFinite := by exact equalizerWithSection_isFinite G u
  contains_unit := by exact equalizerWithSection_contains_unit G u

/-- The object map of `equalizerWithSection G u` is `residueMap G u`. -/
theorem equalizerWithSection_a {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    (equalizerWithSection G u).a = residueMap G u :=
  rfl

/-- The morphism `u' : Spec(κ(u)) ⟶ U'` classifying the pair `(u, Z_u)`. -/
def strongSplittingHom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [StrongSplitting G u] :
    ofOver (residueOver G u) ⟶
      (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  GroupoidAlgebraicSpace.withSectionHom (GroupoidAlgebraicSpace.ofScheme G)
    (equalizerWithSection G u)

/-- The classifying morphism `u'` lies over `u : Spec(κ(u)) ⟶ U`. -/
theorem strongSplittingHom_liesOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    strongSplittingHom G u ≫
        GroupoidAlgebraicSpace.finitePartToU (GroupoidAlgebraicSpace.ofScheme G) =
      residueMap G u :=
  sorry

/-- The `|X|` point determined by a `Spec(κ(u))`-valued morphism into `X`. -/
def residueFieldPoint {S : Scheme.{u}} {X : AlgebraicSpace S} (G : GroupoidScheme S)
    (u : G.U.left) (u' : ofOver (residueOver G u) ⟶ X) : Points X :=
  Points.mk
    (FieldValuedPoint.of (Scheme.FieldValuedPoint.residuePoint u).K
      (residueOver G u).hom u')

/-- The morphism of `residueFieldPoint G u u'` is `u'`. -/
theorem residueFieldPoint_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (G : GroupoidScheme S) (u : G.U.left) (u' : ofOver (residueOver G u) ⟶ X) :
    (FieldValuedPoint.of (Scheme.FieldValuedPoint.residuePoint u).K
        (residueOver G u).hom u').hom =
      u' :=
  rfl

/-- Compatibility of an object-space morphism with the structure map of `ofScheme G`. -/
private theorem objectRestrictionHom_w {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : AlgebraicSpace S} (g : U' ⟶ ofOver G.U) :
    g ≫ (GroupoidAlgebraicSpace.ofScheme G).U.hom =
      (Over.mk (g ≫ (GroupoidAlgebraicSpace.ofScheme G).U.hom)).hom :=
  rfl

/-- An algebraic-space morphism `U' ⟶ U` as a morphism over the base of `ofScheme G`. -/
def objectRestrictionHom {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : AlgebraicSpace S} (g : U' ⟶ ofOver G.U) :
    Over.mk (g ≫ (GroupoidAlgebraicSpace.ofScheme G).U.hom) ⟶
      (GroupoidAlgebraicSpace.ofScheme G).U :=
  Over.homMk g (by exact objectRestrictionHom_w G g)

/-- The underlying morphism of `objectRestrictionHom G g` is `g`. -/
theorem objectRestrictionHom_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : AlgebraicSpace S} (g : U' ⟶ ofOver G.U) :
    (objectRestrictionHom G g).left = g :=
  rfl

/-- The point of `|U'|` determined by the residue-field morphism `u'`. -/
def strongSplittingResiduePoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    Points (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  residueFieldPoint G u (strongSplittingHom G u)

/-- `strongSplittingResiduePoint` is the residue-field point of
`strongSplittingHom`. -/
theorem strongSplittingResiduePoint_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    strongSplittingResiduePoint G u =
      residueFieldPoint G u (strongSplittingHom G u) :=
  rfl

end AlgebraicGeometry.GroupoidScheme
