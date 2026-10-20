/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Map
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.FiniteLimits
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering
public import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-target hypercoverings

This leaf owns the topology-relative hypercovering datum: a simplicial fixed-target
formal coproduct family with a covering degree-zero term and covering matching maps.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C}

/-- A simplicial fixed-target family satisfies the hypercovering condition when its degree-zero
family and all of its matching maps are covering. -/
@[stacks 01G5 "hypercovering condition"]
def IsHypercovering {X : C}
    (J : GrothendieckTopology C)
  (K : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)) : Prop :=
  (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X ∧
    ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J
        (SimplicialObject.matchingMap K n)

/-- The hypercovering condition is exactly its degree-zero and higher matching-map clauses. -/
theorem isHypercovering_iff {X : C}
    (J : GrothendieckTopology C)
    (K : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)) :
    IsHypercovering J K ↔
      (K.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X ∧
        ∀ n : ℕ,
          SemiRepresentableFamily.OverFamily.covering J
            (SimplicialObject.matchingMap K n) := sorry

/-- A hypercovering of `X` is a simplicial fixed-target family whose degree-zero family and
all higher matching maps are covering. -/
@[stacks 01G5 "hypercovering"]
structure Hypercovering (J : GrothendieckTopology C) (X : C) where
  /-- The underlying simplicial object of fixed-target formal coproduct families. -/
  toSimplicialObject :
    SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)
  /-- The degree-zero family generates a covering sieve on `X`. -/
  zero_isCovering :
    (toSimplicialObject.obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X
  /-- Every comparison to a truncated coskeleton is a covering morphism. -/
  succ_isCovering (n : ℕ) :
    SemiRepresentableFamily.OverFamily.covering J
      (SimplicialObject.matchingMap toSimplicialObject n)

namespace Hypercovering

variable {X : C}

/-- A hypercovering coerces to its underlying simplicial object. -/
instance instCoeToSimplicialObject :
    CoeOut (Hypercovering.{w} J X)
      (SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X)) where
  coe K := K.toSimplicialObject

/-- The fixed-target family in degree `n` of a hypercovering. -/
abbrev family (K : Hypercovering.{w} J X) (n : ℕ) :
    SemiRepresentableFamily.OverFamily.{v, u, w} X :=
  K.toSimplicialObject.obj (op <| SimplexCategory.mk n)

/-- The degree-family abbreviation unfolds to the corresponding simplicial object term. -/
@[simp] theorem family_def (K : Hypercovering.{w} J X) (n : ℕ) :
    K.family n = K.toSimplicialObject.obj (op <| SimplexCategory.mk n) := sorry

/-- The underlying simplicial object of a hypercovering satisfies the hypercovering predicate. -/
theorem isHypercovering (K : Hypercovering.{w} J X) :
    IsHypercovering J K.toSimplicialObject := sorry

/-- Regard a bundled hypercovering as an arbitrary simplicial fixed-target family satisfying
the hypercovering predicate. -/
def toSubtype (K : Hypercovering.{w} J X) :
    { L : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X) //
      IsHypercovering J L } :=
  ⟨K.toSimplicialObject, K.zero_isCovering, K.succ_isCovering⟩

/-- Bundle any simplicial fixed-target family satisfying the hypercovering predicate. -/
def ofSubtype
    (K : { L : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X) //
      IsHypercovering J L }) : Hypercovering.{w} J X where
  toSimplicialObject := K.1
  zero_isCovering := K.2.1
  succ_isCovering := K.2.2

/-- Bundling the predicate view of a hypercovering returns the original hypercovering. -/
theorem ofSubtype_toSubtype (K : Hypercovering.{w} J X) :
    ofSubtype (toSubtype K) = K := sorry

/-- Taking the predicate view of a bundled predicate witness returns the original witness. -/
theorem toSubtype_ofSubtype
    (K : { L : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X) //
      IsHypercovering J L }) :
    toSubtype (ofSubtype K) = K := sorry

/-- Remark 25.3.8 (Tag 01G8): bundled hypercoverings are exactly all simplicial fixed-target
families satisfying the hypercovering predicate, rather than a chosen cofinal subsystem. -/
@[stacks 01G8 "all hypercoverings"]
def equivSubtype :
    Hypercovering.{w} J X ≃
      { L : SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X) //
        IsHypercovering J L } where
  toFun := toSubtype
  invFun := ofSubtype
  left_inv := ofSubtype_toSubtype
  right_inv := toSubtype_ofSubtype

/-- Lemma 25.3.7 (Tag 01G7): all hypercoverings in a fixed family universe form a type in an
explicit successor-universe bound. -/
@[stacks 01G7 "small type of hypercoverings"]
instance small (X : C) :
    Small.{max (u + 1) (v + 1) (w + 1)} (Hypercovering.{w} J X) := sorry

end Hypercovering

end CategoryTheory
