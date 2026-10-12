/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import ReasLib.AlgebraicTopology.SimplicialSet.Objwise
public import ReasLib.AlgebraicTopology.SimplicialSet.Dimension
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Pushout

/-!
# Pushouts of simplicial sets

This file records closure properties of simplicial-set pushouts that follow degreewise from
pushouts of types. The statements use the canonical pushout in the functor category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe u

namespace SSet

namespace evaluation

/-- Evaluation of a simplicial-set pushout is canonically isomorphic to the corresponding
type-theoretic pushout. -/
@[stacks 016W "evaluation to the type-theoretic pushout"]
noncomputable def pushoutIso {U V W : SSet.{u}}
    (a : U ⟶ V) (b : U ⟶ W) (Δ : SimplexCategoryᵒᵖ) :
    (pushout a b).obj Δ ≅ Types.Pushout (a.app Δ) (b.app Δ) :=
  FunctorCategory.evaluation.pushoutIso a b Δ ≪≫
    IsColimit.coconePointUniqueUpToIso
      (pushout.isColimit (a.app Δ) (b.app Δ))
      (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))

namespace pushoutIso

/-- The inverse pointwise pushout comparison sends the explicit left inclusion to the evaluated
left simplicial pushout inclusion. -/
theorem inl_inv {U V W : SSet.{u}} (a : U ⟶ V) (b : U ⟶ W)
    (Δ : SimplexCategoryᵒᵖ) :
    Types.Pushout.inl (a.app Δ) (b.app Δ) ≫ (pushoutIso a b Δ).inv =
      (pushout.inl a b).app Δ := sorry

/-- The inverse pointwise pushout comparison sends the explicit right inclusion to the evaluated
right simplicial pushout inclusion. -/
theorem inr_inv {U V W : SSet.{u}} (a : U ⟶ V) (b : U ⟶ W)
    (Δ : SimplexCategoryᵒᵖ) :
    Types.Pushout.inr (a.app Δ) (b.app Δ) ≫ (pushoutIso a b Δ).inv =
      (pushout.inr a b).app Δ := sorry

/-- The pointwise pushout comparison sends a simplex from the left target to its explicit
type-theoretic pushout representative. -/
@[simp]
theorem hom_inl_apply {U V W : SSet.{u}} (a : U ⟶ V) (b : U ⟶ W)
    (Δ : SimplexCategoryᵒᵖ) (v : V.obj Δ) :
    (pushoutIso a b Δ).hom ((pushout.inl a b).app Δ v) =
      Types.Pushout.inl (a.app Δ) (b.app Δ) v := sorry

/-- The pointwise pushout comparison sends a simplex from the right target to its explicit
type-theoretic pushout representative. -/
@[simp]
theorem hom_inr_apply {U V W : SSet.{u}} (a : U ⟶ V) (b : U ⟶ W)
    (Δ : SimplexCategoryᵒᵖ) (w : W.obj Δ) :
    (pushoutIso a b Δ).hom ((pushout.inr a b).app Δ w) =
      Types.Pushout.inr (a.app Δ) (b.app Δ) w := sorry

end pushoutIso

end evaluation

/-- A pushout of simplicial sets is degreewise finite when both target legs are degreewise
finite. No finiteness hypothesis on the source of the span is needed. -/
@[stacks 017N "objectwise finiteness of simplicial-set pushouts"]
instance pushout.objFinite {U V W : SSet.{u}} [V.ObjFinite] [W.ObjFinite]
    (a : U ⟶ V) (b : U ⟶ W) : (pushout a b).ObjFinite := sorry

/-- A vertex of the left target gives a vertex of the simplicial-set pushout. -/
@[stacks 017N "nonemptiness of simplicial-set pushouts from the left"]
instance pushout.nonempty_of_left {U V W : SSet.{u}} [V.Nonempty]
    (a : U ⟶ V) (b : U ⟶ W) : (pushout a b).Nonempty := sorry

/-- A vertex of the right target gives a vertex of the simplicial-set pushout. -/
@[stacks 017N "nonemptiness of simplicial-set pushouts from the right"]
instance pushout.nonempty_of_right {U V W : SSet.{u}} [W.Nonempty]
    (a : U ⟶ V) (b : U ⟶ W) : (pushout a b).Nonempty := sorry

/-- A pushout of simplicial sets has dimension at most the maximum of dimension bounds for its
two target legs. -/
@[stacks 017N "dimension bound for simplicial-set pushouts"]
theorem pushout.hasDimensionLE {U V W : SSet.{u}} (a : U ⟶ V) (b : U ⟶ W)
    (dV dW : ℕ) [V.HasDimensionLE dV] [W.HasDimensionLE dW] :
    (pushout a b).HasDimensionLE (max dV dW) := sorry

/-- Eventual degeneracy is closed under pushouts of simplicial sets. -/
@[stacks 017N "eventual degeneracy of simplicial-set pushouts"]
theorem EventuallyDegenerate.pushout {U V W : SSet.{u}} (a : U ⟶ V) (b : U ⟶ W)
    (hV : V.EventuallyDegenerate) (hW : W.EventuallyDegenerate) :
    (pushout a b).EventuallyDegenerate := sorry

/-- Eventual degeneracy is inferred for simplicial-set pushouts from the two target legs. -/
@[stacks 017N "eventual-degeneracy instance for simplicial-set pushouts"]
instance pushout.eventuallyDegenerate {U V W : SSet.{u}}
    [V.EventuallyDegenerate] [W.EventuallyDegenerate]
    (a : U ⟶ V) (b : U ⟶ W) : (pushout a b).EventuallyDegenerate := sorry

end SSet
