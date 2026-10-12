/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback

/-!
# Relations on an algebraic space over a base

This module records pre-relations and relations in the slice category of algebraic spaces over a
base algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Binary products in the slice of algebraic spaces over `B` are obtained from pullbacks in
`AlgebraicSpace S`. -/
instance instHasBinaryProducts_over {S : Scheme.{u}} (B : AlgebraicSpace S) :
    HasBinaryProducts (Over B) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- A pre-relation on `U` over `B` is an object over `U ⨯ U` in `Over B`. -/
abbrev PreRelation {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :=
  Over (U ⨯ U)

namespace PreRelation

/-- Construct a pre-relation from its source object and its map to `U ⨯ U`. -/
def ofHom {S : Scheme.{u}} {B : AlgebraicSpace S} {U R : Over B} (j : R ⟶ U ⨯ U) :
    PreRelation U :=
  Over.mk j

/-- The structure morphism of the pre-relation constructed from `j` is `j`. -/
theorem ofHom_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U R : Over B} (j : R ⟶ U ⨯ U) :
    (ofHom j).hom = j := sorry

/-- The first projection of a pre-relation. -/
def t {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.fst

/-- The second projection of a pre-relation. -/
def s {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.snd

/-- The map defining a pre-relation is the product lift of its two projections. -/
theorem hom_eq_prod_lift {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.hom = prod.lift P.t P.s := sorry

/-- The image relation on the `T/B`-valued points of `U`, for a scheme `T` over `S` equipped with
a structure map to `B`. -/
def pointRel {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    {T : Over S} (τ : ofOver T ⟶ B) :
    (Over.mk τ ⟶ U) → (Over.mk τ ⟶ U) → Prop :=
  fun x y ↦ ∃ r : Over.mk τ ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y

/-- Two `T/B`-valued points are related exactly when they lift to a point of the source. -/
theorem pointRel_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    {T : Over S} (τ : ofOver T ⟶ B) (x y : Over.mk τ ⟶ U) :
    P.pointRel τ x y ↔ ∃ r : Over.mk τ ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y := sorry

/-- A pre-relation is a pre-equivalence relation when every induced point relation on schemes over
`B` is an equivalence relation. -/
def IsPreEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop :=
  ∀ {T : Over S} (τ : ofOver T ⟶ B), Equivalence (P.pointRel τ)

/-- The pointwise characterization of a pre-equivalence relation. -/
theorem isPreEquivalence_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.IsPreEquivalence ↔ ∀ {T : Over S} (τ : ofOver T ⟶ B), Equivalence (P.pointRel τ) := sorry

end PreRelation

/-- A relation on `U` over `B` is a monomorphism into `U ⨯ U` in `Over B`. -/
abbrev Relation {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :=
  MonoOver (U ⨯ U)

namespace Relation

/-- Forget the monomorphism property of a relation. -/
def toPreRelation {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (Q : Relation U) :
    PreRelation U :=
  Q.obj

/-- Forgetting a relation preserves its defining arrow. -/
theorem toPreRelation_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (Q : Relation U) :
    Q.toPreRelation.hom = Q.arrow := sorry

/-- Regard a pre-relation with monic defining arrow as a relation. -/
def ofPreRelation {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] : Relation U :=
  MonoOver.mk P.hom

/-- The relation obtained from a monic pre-relation has the same defining arrow. -/
theorem ofPreRelation_arrow {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [Mono P.hom] :
    (ofPreRelation P).arrow = P.hom := sorry

end Relation

namespace PreRelation

/-- Internal equivalence is equivalent to being both a relation and a pre-equivalence relation. -/
theorem isEquivalenceRelation_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔ Mono P.hom ∧ P.IsPreEquivalence := sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
