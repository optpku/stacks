/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import ReasLib.CategoryTheory.Limits.Over.Products

/-!
# Relations on an algebraic space over a base

This module records pre-relations and relations in the slice category of algebraic spaces over a
base algebraic space.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

/-- A pre-relation on `U` over `B` is an object over `U ⨯ U` in `Over B`. -/
abbrev PreRelation {B : AlgebraicSpace S} (U : Over B) :=
  Over (U ⨯ U)

namespace PreRelation

/-- Construct a pre-relation from its source object and its map to `U ⨯ U`. -/
def ofHom {B : AlgebraicSpace S} {U R : Over B} (j : R ⟶ U ⨯ U) : PreRelation U :=
  Over.mk j

/-- The structure morphism of the pre-relation constructed from `j` is `j`. -/
theorem ofHom_hom {B : AlgebraicSpace S} {U R : Over B} (j : R ⟶ U ⨯ U) :
    (ofHom j).hom = j := sorry

/-- The first projection of a pre-relation. -/
def t {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.fst

/-- The second projection of a pre-relation. -/
def s {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.snd

/-- The map defining a pre-relation is the product lift of its two projections. -/
theorem hom_eq_prod_lift {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    P.hom = prod.lift P.t P.s := sorry

/-- The map on `T/B`-valued points induced by the two projections of a pre-relation. -/
def pointMap {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) (T : Over B) :
    (T ⟶ P.left) → (T ⟶ U) × (T ⟶ U) :=
  fun r ↦ (r ≫ P.t, r ≫ P.s)

/-- The point map sends `r` to its composites with the two projections. -/
theorem pointMap_apply {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (T : Over B) (r : T ⟶ P.left) :
    P.pointMap T r = (r ≫ P.t, r ≫ P.s) := sorry

/-- The image relation on the `T/B`-valued points of `U`. -/
def pointRel {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) (T : Over B) :
    (T ⟶ U) → (T ⟶ U) → Prop :=
  fun x y ↦ ∃ r : T ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y

/-- Two `T/B`-valued points are related exactly when they lift to a point of the source. -/
theorem pointRel_iff {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (T : Over B) (x y : T ⟶ U) :
    P.pointRel T x y ↔ ∃ r : T ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y := sorry

/-- A pre-relation is a pre-equivalence relation when the image of `j` on `T`-valued points is
an equivalence relation for every scheme `T` over `B`. -/
def IsPreEquivalence {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : Prop :=
  ∀ (T : Over S) (σ : ofOver T ⟶ B), Equivalence (P.pointRel (Over.mk σ))

/-- The pointwise characterization of a pre-equivalence relation on scheme-valued points over `B`. -/
theorem isPreEquivalence_iff {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    P.IsPreEquivalence ↔
      ∀ (T : Over S) (σ : ofOver T ⟶ B), Equivalence (P.pointRel (Over.mk σ)) := sorry

/-- Under a monic defining map, a pre-equivalence relation is equivalently tested on all
algebraic spaces over `B`. -/
theorem isPreEquivalence_iff_points {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [Mono P.hom] :
    P.IsPreEquivalence ↔ ∀ T : Over B, Equivalence (P.pointRel T) := sorry

/-- An equivalence relation has injective point maps and equivalence-relation image relations on
all scheme-valued points over the base. -/
def IsEquivalence {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : Prop :=
  ∀ (T : Over S) (σ : ofOver T ⟶ B),
    Function.Injective (P.pointMap (Over.mk σ)) ∧
      Equivalence (P.pointRel (Over.mk σ))

end PreRelation

/-- A relation on `U` over `B` is a monomorphism into `U ⨯ U` in `Over B`. -/
abbrev Relation {B : AlgebraicSpace S} (U : Over B) :=
  MonoOver (U ⨯ U)

namespace Relation

/-- Forget the monomorphism property of a relation. -/
def toPreRelation {B : AlgebraicSpace S} {U : Over B} (Q : Relation U) : PreRelation U :=
  Q.obj

/-- Forgetting a relation preserves its defining arrow. -/
theorem toPreRelation_hom {B : AlgebraicSpace S} {U : Over B} (Q : Relation U) :
    Q.toPreRelation.hom = Q.arrow := sorry

/-- Regard a pre-relation with monic defining arrow as a relation. -/
def ofPreRelation {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] : Relation U :=
  MonoOver.mk P.hom

/-- The relation obtained from a monic pre-relation has the same defining arrow. -/
theorem ofPreRelation_arrow {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] :
    (ofPreRelation P).arrow = P.hom := sorry

end Relation

namespace PreRelation

/-- A monic defining map makes the two projections of a pre-relation jointly monic. -/
instance instJointlyMono₂ {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] : JointlyMono₂ P.t P.s := sorry

/-- An internal equivalence relation has a monic defining map to `U ⨯ U`. -/
instance instMonoHom {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : Mono P.hom := sorry

/-- Internal equivalence is equivalent to being both a relation and a pre-equivalence relation. -/
theorem isEquivalenceRelation_iff {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔ Mono P.hom ∧ P.IsPreEquivalence := sorry

/-- Internal equivalence is characterized on every algebraic space of points over the base by
injectivity of the point map and the equivalence-relation property of its image. -/
theorem isEquivalenceRelation_iff_points {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔
      ∀ T : Over B, Function.Injective (P.pointMap T) ∧ Equivalence (P.pointRel T) := sorry

/-- Internal equivalence is characterized on scheme-valued points over `B` by injectivity of the
point map and the equivalence-relation property of its image. -/
theorem isEquivalenceRelation_iff_schemePoints {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔
      ∀ (T : Over S) (σ : ofOver T ⟶ B),
        Function.Injective (P.pointMap (Over.mk σ)) ∧
          Equivalence (P.pointRel (Over.mk σ)) := sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
