/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Relations on a scheme over a base

This module records pre-relations and relations in the slice category of schemes over a base.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A pre-relation on `U` over `S` is an object over `U ⨯ U` in `Over S`. -/
abbrev PreRelation {S : Scheme.{u}} (U : Over S) := Over (U ⨯ U)

namespace PreRelation

/-- Construct a pre-relation from its source object and its map to `U ⨯ U`. -/
def ofHom {S : Scheme.{u}} {U R : Over S} (j : R ⟶ U ⨯ U) : PreRelation U :=
  Over.mk j

/-- The structure morphism of the pre-relation constructed from `j` is `j`. -/
theorem ofHom_hom {S : Scheme.{u}} {U R : Over S} (j : R ⟶ U ⨯ U) :
    (ofHom j).hom = j := sorry

/-- The first projection of a pre-relation. -/
def t {S : Scheme.{u}} {U : Over S} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.fst

/-- The second projection of a pre-relation. -/
def s {S : Scheme.{u}} {U : Over S} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.snd

/-- The map defining a pre-relation is the product lift of its two projections. -/
theorem hom_eq_prod_lift {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    P.hom = prod.lift P.t P.s := sorry

/-- The map on `T/S`-valued points induced by the two projections of a pre-relation. -/
def pointMap {S : Scheme.{u}} {U : Over S} (P : PreRelation U) (T : Over S) :
    (T ⟶ P.left) → (T ⟶ U) × (T ⟶ U) :=
  fun r ↦ (r ≫ P.t, r ≫ P.s)

/-- The point map sends `r` to its composites with the two projections. -/
theorem pointMap_apply {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    (T : Over S) (r : T ⟶ P.left) :
    P.pointMap T r = (r ≫ P.t, r ≫ P.s) := sorry

/-- The image relation on the `T/S`-valued points of `U`. -/
def pointRel {S : Scheme.{u}} {U : Over S} (P : PreRelation U) (T : Over S) :
    (T ⟶ U) → (T ⟶ U) → Prop :=
  fun x y ↦ ∃ r : T ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y

/-- Two `T/S`-valued points are related exactly when they lift to a point of the source. -/
theorem pointRel_iff {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    (T : Over S) (x y : T ⟶ U) :
    P.pointRel T x y ↔ ∃ r : T ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y := sorry

/-- A pre-relation is a pre-equivalence relation when every induced point relation is an
equivalence relation. -/
def IsPreEquivalence {S : Scheme.{u}} {U : Over S} (P : PreRelation U) : Prop :=
  ∀ T : Over S, Equivalence (P.pointRel T)

/-- The pointwise characterization of a pre-equivalence relation. -/
theorem isPreEquivalence_iff {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    P.IsPreEquivalence ↔ ∀ T : Over S, Equivalence (P.pointRel T) := sorry

end PreRelation

/-- A relation on `U` over `S` is a monomorphism into `U ⨯ U` in `Over S`. -/
abbrev Relation {S : Scheme.{u}} (U : Over S) := MonoOver (U ⨯ U)

namespace Relation

/-- Forget the monomorphism property of a relation. -/
def toPreRelation {S : Scheme.{u}} {U : Over S} (Q : Relation U) : PreRelation U :=
  Q.obj

/-- Forgetting a relation preserves its defining arrow. -/
theorem toPreRelation_hom {S : Scheme.{u}} {U : Over S} (Q : Relation U) :
    Q.toPreRelation.hom = Q.arrow := sorry

/-- Regard a pre-relation with monic defining arrow as a relation. -/
def ofPreRelation {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [Mono P.hom] : Relation U :=
  MonoOver.mk P.hom

/-- The relation obtained from a monic pre-relation has the same defining arrow. -/
theorem ofPreRelation_arrow {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [Mono P.hom] :
    (ofPreRelation P).arrow = P.hom := sorry

end Relation

namespace PreRelation

/-- A monic defining map makes the two projections of a pre-relation jointly monic. -/
instance instJointlyMono₂ {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [Mono P.hom] : JointlyMono₂ P.t P.s := sorry

/-- An internal equivalence relation has a monic defining map to `U ⨯ U`. -/
instance instMonoHom {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : Mono P.hom := sorry

/-- Internal equivalence is equivalent to being both a relation and a pre-equivalence relation. -/
theorem isEquivalenceRelation_iff {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔ Mono P.hom ∧ P.IsPreEquivalence := sorry

/-- Internal equivalence is characterized on every scheme of points over the base by injectivity
of the point map and the equivalence-relation property of its image. -/
theorem isEquivalenceRelation_iff_points {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔
      ∀ T : Over S, Function.Injective (P.pointMap T) ∧ Equivalence (P.pointRel T) := sorry

end PreRelation

end AlgebraicGeometry.Scheme
