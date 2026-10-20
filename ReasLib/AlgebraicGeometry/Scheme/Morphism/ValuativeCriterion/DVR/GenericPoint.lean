/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR
public import Mathlib.Tactic.CrossRefAttribute

/-!
# DVR-valuative squares from residue fields

This leaf packages DVR-valuative squares whose generic map is the canonical
map from the residue field of a specified source point. The primitive API works
over any set of source points; the generic-point criteria are its standard
specializations.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A DVR-valuative commutative square whose generic map is the residue-field map of a source
point in `points`. -/
@[stacks 0CM2 "DVR-valuative square at a prescribed source point"]
structure DvrValuativeCommSqAt {X S : Scheme.{u}} (f : X ⟶ S) (points : Set X) where
  /-- The source point specifying the generic map. -/
  sourcePoint : X
  /-- The source point belongs to the prescribed test set. -/
  sourcePoint_mem : sourcePoint ∈ points
  /-- The discrete valuation ring. -/
  R : Type u
  /-- The commutative-ring structure on the discrete valuation ring. -/
  [commRing : CommRing R]
  /-- The domain structure on the discrete valuation ring. -/
  [domain : IsDomain R]
  /-- The discrete-valuation-ring structure. -/
  [dvr : IsDiscreteValuationRing R]
  /-- The algebra structure from the DVR to the residue field of `sourcePoint`. -/
  [algebra : Algebra R (X.residueField sourcePoint)]
  /-- The residue field is the fraction field of the DVR. -/
  [isFractionRing : IsFractionRing R (X.residueField sourcePoint)]
  /-- The map from the spectrum of the DVR to the target. -/
  toTarget : Spec (CommRingCat.of R) ⟶ S
  /-- The commutative square over `f`. -/
  commSq : CommSq (X.fromSpecResidueField sourcePoint)
    (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField sourcePoint)))) f toTarget

attribute [stacks 0CM2 "DVR-valuative square source point"] DvrValuativeCommSqAt.sourcePoint
attribute [stacks 0CM2 "DVR-valuative square source-point membership"]
  DvrValuativeCommSqAt.sourcePoint_mem
attribute [stacks 0CM2 "DVR-valuative square ring"] DvrValuativeCommSqAt.R
attribute [stacks 0CM2 "DVR-valuative square target map"] DvrValuativeCommSqAt.toTarget
attribute [stacks 0CM2 "DVR-valuative square commutativity"] DvrValuativeCommSqAt.commSq

namespace DvrValuativeCommSqAt

/-- Forget the prescribed source point and retain the underlying DVR-valuative square. -/
@[stacks 0CM2 "forget source-point data from a DVR-valuative square"]
noncomputable def toDvrValuativeCommSq {X S : Scheme.{u}} {f : X ⟶ S} {points : Set X}
    (sq : DvrValuativeCommSqAt f points) : DvrValuativeCommSq f :=
  ⟨{ R := sq.R
     commRing := sq.commRing
     domain := sq.domain
     valuationRing := @of_isDiscreteValuationRing sq.R sq.commRing sq.domain sq.dvr
     K := X.residueField sq.sourcePoint
     field := inferInstance
     algebra := sq.algebra
     isFractionRing := sq.isFractionRing
     i₁ := X.fromSpecResidueField sq.sourcePoint
     i₂ := sq.toTarget
     commSq := sq.commSq }, sq.dvr⟩

/-- A pointwise DVR-valuative square remembers membership of its source point and has the
canonical residue-field map and stored target map as the two horizontal maps of its underlying
valuative square. -/
@[stacks 0CM2 "pointwise DVR-valuative square specification"]
theorem spec {X S : Scheme.{u}} {f : X ⟶ S} {points : Set X}
    (sq : DvrValuativeCommSqAt f points) :
    sq.sourcePoint ∈ points ∧
      sq.toDvrValuativeCommSq.toValuativeCommSq.i₁ =
        X.fromSpecResidueField sq.sourcePoint ∧
      sq.toDvrValuativeCommSq.toValuativeCommSq.i₂ = sq.toTarget := sorry

end DvrValuativeCommSqAt

/- DVR-valuative criteria restricted to residue-field maps from a prescribed set of source
points. -/
namespace DvrValuativeCriterionAt

/-- Every prescribed pointwise DVR-valuative square over `f` admits a lift. -/
@[stacks 05JY "pointwise DVR valuative existence criterion"]
def Existence {X S : Scheme.{u}} (f : X ⟶ S) (points : Set X) : Prop :=
  ∀ sq : DvrValuativeCommSqAt f points, sq.commSq.HasLift

/-- Every prescribed pointwise DVR-valuative square over `f` has at most one lift. -/
@[stacks 0207 "pointwise DVR valuative uniqueness criterion"]
def Uniqueness {X S : Scheme.{u}} (f : X ⟶ S) (points : Set X) : Prop :=
  ∀ sq : DvrValuativeCommSqAt f points, Subsingleton sq.commSq.LiftStruct

/-- Every prescribed pointwise DVR-valuative square over `f` has a lift and at most one lift. -/
@[stacks 0208 "pointwise DVR valuative exists-unique criterion"]
def ExistsUnique {X S : Scheme.{u}} (f : X ⟶ S) (points : Set X) : Prop :=
  ∀ sq : DvrValuativeCommSqAt f points,
    sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct

/-- Pointwise DVR existence-and-uniqueness is equivalent to its separate existence and uniqueness
conditions. -/
@[stacks 0208 "pointwise DVR valuative criterion decomposition"]
theorem existsUnique_iff {X S : Scheme.{u}} {f : X ⟶ S} {points : Set X} :
    ExistsUnique f points ↔ Existence f points ∧ Uniqueness f points := sorry

/-- Pointwise DVR existence-and-uniqueness implies pointwise DVR existence. -/
@[stacks 05JY "pointwise DVR valuative existence projection"]
theorem existence {X S : Scheme.{u}} {f : X ⟶ S} {points : Set X}
    (h : ExistsUnique f points) : Existence f points := sorry

/-- Pointwise DVR existence-and-uniqueness implies pointwise DVR uniqueness. -/
@[stacks 0207 "pointwise DVR valuative uniqueness projection"]
theorem uniqueness {X S : Scheme.{u}} {f : X ⟶ S} {points : Set X}
    (h : ExistsUnique f points) : Uniqueness f points := sorry

end DvrValuativeCriterionAt

/-- The DVR-valuative existence condition tested at generic points of irreducible components. -/
abbrev GenericPointDvrValuativeCriterionExistence {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  DvrValuativeCriterionAt.Existence f (genericPoints X)

/-- The DVR-valuative uniqueness condition tested at generic points of irreducible components. -/
abbrev GenericPointDvrValuativeCriterionUniqueness {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  DvrValuativeCriterionAt.Uniqueness f (genericPoints X)

/-- The DVR-valuative existence-and-uniqueness condition tested at generic points of irreducible
components. -/
abbrev GenericPointDvrValuativeCriterionExistsUnique {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  DvrValuativeCriterionAt.ExistsUnique f (genericPoints X)

end AlgebraicGeometry
