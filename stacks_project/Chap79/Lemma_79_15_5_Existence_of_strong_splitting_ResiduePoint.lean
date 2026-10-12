/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap79.«79_12_0_2_FinitePart»
public import stacks_project.Chap79.Definition_79_15_1_Splitting
public import stacks_project.Chap79.Lemma_79_14_1_Groupoid
public import stacks_project.Chap79.Lemma_79_14_1_Section
public import stacks_project.Chap79.Lemma_79_15_5_Existence_of_strong_splitting_OfScheme
public import stacks_project.Chap79.Situation_79_15_2_Strong_splitting

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

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The finite-part morphism `U' ⟶ U` of a groupoid scheme is étale. -/
instance etale_finitePartToU_ofScheme {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsSeparated G.s.left] [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
    [IsSeparated G.t.left] [AlgebraicGeometry.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.Etale (finitePartToU (ofScheme G)) :=
  sorry

/-- The original identity arrow and the diagonal of `U'` define a point of the restricted
arrow pullback. -/
theorem pullbackIdentity_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (g ≫ G.e) ≫ G.toPreRelation.hom = diag U' ≫ prod.map g g :=
  sorry

/-- The identity-arrow map of the restricted groupoid. -/
def pullbackIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    U' ⟶ ((Over.pullback (prod.map g g)).obj G.toPreRelation).left :=
  pullback.lift (g ≫ G.e) (diag U') (pullbackIdentity_condition G g)

/-- Applying the original inverse and exchanging the two endpoints defines an arrow of the
restricted groupoid. -/
theorem pullbackInverse_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullback.fst G.toPreRelation.hom (prod.map g g) ≫ G.i) ≫ G.toPreRelation.hom =
      prod.lift
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        prod.map g g :=
  sorry

/-- The inverse-arrow map of the restricted groupoid. -/
def pullbackInverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    ((Over.pullback (prod.map g g)).obj G.toPreRelation).left ⟶
      ((Over.pullback (prod.map g g)).obj G.toPreRelation).left :=
  pullback.lift (pullback.fst G.toPreRelation.hom (prod.map g g) ≫ G.i)
    (prod.lift
      (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
      (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst))
    (pullbackInverse_condition G g)

/-- The images in `G` of two composable restricted arrows remain composable. -/
theorem pullbackCompositionToArrows_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    (pullback.fst
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        pullback.fst G.toPreRelation.hom (prod.map g g)) ≫ G.s =
      (pullback.snd
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        pullback.fst G.toPreRelation.hom (prod.map g g)) ≫ G.t :=
  sorry

/-- Compose a pair of restricted arrows in the original groupoid. -/
def pullbackCompositionToArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullback
        (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
        (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ⟶
      G.R :=
  pullback.lift
      (pullback.fst
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        pullback.fst G.toPreRelation.hom (prod.map g g))
      (pullback.snd
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        pullback.fst G.toPreRelation.hom (prod.map g g))
      (pullbackCompositionToArrows_condition G g) ≫ G.c

/-- The original composite and its two endpoints define a point of the restricted arrow
pullback. -/
theorem pullbackComposition_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullbackCompositionToArrows G g ≫ G.toPreRelation.hom =
      prod.lift
          (pullback.fst
              (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
              (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
            (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst))
          (pullback.snd
              (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
              (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
            (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)) ≫
        prod.map g g :=
  sorry

/-- The canonical composition law on the restricted arrow space. -/
def pullbackComposition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    pullback
        (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
        (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ⟶
      ((Over.pullback (prod.map g g)).obj G.toPreRelation).left :=
  pullback.lift (pullbackCompositionToArrows G g)
    (prod.lift
      (pullback.fst
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst))
      (pullback.snd
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)
          (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst) ≫
        (((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd)))
    (pullbackComposition_condition G g)

/-- Restriction of a groupoid in algebraic spaces along a morphism to its object space. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    GroupoidAlgebraicSpace B where
  U := U'
  R := ((Over.pullback (prod.map g g)).obj G.toPreRelation).left
  s := ((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.snd
  t := ((Over.pullback (prod.map g g)).obj G.toPreRelation).hom ≫ prod.fst
  c := pullbackComposition G g
  e := pullbackIdentity G g
  i := pullbackInverse G g
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupoidScheme

/-- The residue-field scheme `Spec(κ(u))` of an object point, as a scheme over `S`. -/
def residueOver {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) : Over S :=
  Over.mk (G.U.left.fromSpecResidueField u ≫ G.U.hom)

/-- The structure morphism of `residueOver G u` is `Spec(κ(u)) ⟶ S`. -/
theorem residueOver_hom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    (residueOver G u).hom = G.U.left.fromSpecResidueField u ≫ G.U.hom :=
  rfl

/-- Compatibility of `fromSpecResidueField u` with the structure morphisms over `S`. -/
theorem residueMap_w {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    G.U.left.fromSpecResidueField u ≫ G.U.hom = (residueOver G u).hom :=
  rfl

/-- The morphism `u : Spec(κ(u)) ⟶ U` as a morphism of algebraic spaces over `S`. -/
def residueMap {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    ofOver (residueOver G u) ⟶ ofOver G.U :=
  ofOverMap (Over.homMk (G.U.left.fromSpecResidueField u) (residueMap_w G u))

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
  is_open' := sorry

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
  isFinite := sorry
  contains_unit := sorry

/-- The object map of `equalizerWithSection G u` is `residueMap G u`. -/
theorem equalizerWithSection_a {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u] :
    (equalizerWithSection G u).a = residueMap G u :=
  rfl

/-- The morphism `u' : Spec(κ(u)) ⟶ U'` classifying the pair `(u, Z_u)`. -/
def strongSplittingHom {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [StrongSplitting G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    ofOver (residueOver G u) ⟶
      (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  GroupoidAlgebraicSpace.withSectionHom (GroupoidAlgebraicSpace.ofScheme G)
    (equalizerWithSection G u)

/-- The classifying morphism `u'` lies over `u : Spec(κ(u)) ⟶ U`. -/
theorem strongSplittingHom_liesOver {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
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
theorem objectRestrictionHom_w {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : AlgebraicSpace S} (g : U' ⟶ ofOver G.U) :
    g ≫ (GroupoidAlgebraicSpace.ofScheme G).U.hom =
      (Over.mk (g ≫ (GroupoidAlgebraicSpace.ofScheme G).U.hom)).hom :=
  rfl

/-- An algebraic-space morphism `U' ⟶ U` as a morphism over the base of `ofScheme G`. -/
def objectRestrictionHom {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : AlgebraicSpace S} (g : U' ⟶ ofOver G.U) :
    Over.mk (g ≫ (GroupoidAlgebraicSpace.ofScheme G).U.hom) ⟶
      (GroupoidAlgebraicSpace.ofScheme G).U :=
  Over.homMk g (objectRestrictionHom_w G g)

/-- The underlying morphism of `objectRestrictionHom G g` is `g`. -/
theorem objectRestrictionHom_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : AlgebraicSpace S} (g : U' ⟶ ofOver G.U) :
    (objectRestrictionHom G g).left = g :=
  rfl

/-- The point of `|U'|` determined by the residue-field morphism `u'`. -/
def strongSplittingResiduePoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    Points (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left :=
  residueFieldPoint G u (strongSplittingHom G u)

/-- `strongSplittingResiduePoint` is the residue-field point of
`strongSplittingHom`. -/
theorem strongSplittingResiduePoint_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) [StrongSplitting G u]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).s.left]
    [AlgebraicSpace.Separated (GroupoidAlgebraicSpace.ofScheme G).t.left]
    [AlgebraicSpace.LocallyOfFiniteType (GroupoidAlgebraicSpace.ofScheme G).t.left] :
    strongSplittingResiduePoint G u =
      residueFieldPoint G u (strongSplittingHom G u) :=
  rfl

end AlgebraicGeometry.GroupoidScheme
