module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Composition of internal equivalence relations

This module constructs and characterizes composition for an internal equivalence relation on a
scheme over a base.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The canonical composition morphism on composable arrows of an internal equivalence relation
over a scheme. -/
def composition {S : Scheme.{u}} {U : Over S} (P : PreRelation U) [IsEquivalenceRelation P.t P.s] :
    pullback P.s P.t ⟶ P.left :=
  let hP : EquivalenceRelation P.t P.s :=
    Classical.choice (show Nonempty (EquivalenceRelation P.t P.s) from
      IsEquivalenceRelation.nonempty_equivalenceRelation)
  let T := hP.toTransitiveRelation
  PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t) (pullback.snd P.s P.t)
      pullback.condition ≫
    T.t

/-- The target of `P.composition` is the target of the first composable arrow. -/
theorem composition_target {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] :
    P.composition ≫ P.t = pullback.fst P.s P.t ≫ P.t := by
  classical
  let hP : EquivalenceRelation P.t P.s :=
    Classical.choice (show Nonempty (EquivalenceRelation P.t P.s) from
      IsEquivalenceRelation.nonempty_equivalenceRelation)
  let T := hP.toTransitiveRelation
  change PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t)
      (pullback.snd P.s P.t) pullback.condition ≫ T.t ≫ P.t =
    pullback.fst P.s P.t ≫ P.t
  rw [T.transitivity₁]
  calc
    PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t) (pullback.snd P.s P.t)
        pullback.condition ≫ T.c.fst ≫ P.t =
      (PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t) (pullback.snd P.s P.t)
          pullback.condition ≫ T.c.fst) ≫ P.t := by simp
    _ = pullback.fst P.s P.t ≫ P.t := by rw [PullbackCone.IsLimit.lift_fst]

/-- The source of `P.composition` is the source of the second composable arrow. -/
theorem composition_source {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] :
    P.composition ≫ P.s = pullback.snd P.s P.t ≫ P.s := by
  classical
  let hP : EquivalenceRelation P.t P.s :=
    Classical.choice (show Nonempty (EquivalenceRelation P.t P.s) from
      IsEquivalenceRelation.nonempty_equivalenceRelation)
  let T := hP.toTransitiveRelation
  change PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t)
      (pullback.snd P.s P.t) pullback.condition ≫ T.t ≫ P.s =
    pullback.snd P.s P.t ≫ P.s
  rw [T.transitivity₂]
  calc
    PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t) (pullback.snd P.s P.t)
        pullback.condition ≫ T.c.snd ≫ P.s =
      (PullbackCone.IsLimit.lift T.isLimit (pullback.fst P.s P.t) (pullback.snd P.s P.t)
          pullback.condition ≫ T.c.snd) ≫ P.s := by simp
    _ = pullback.snd P.s P.t ≫ P.s := by rw [PullbackCone.IsLimit.lift_snd]

/-- The composition morphism is characterized by its target and source maps. -/
theorem composition_spec {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] :
    P.composition ≫ P.t = pullback.fst P.s P.t ≫ P.t ∧
      P.composition ≫ P.s = pullback.snd P.s P.t ≫ P.s :=
  ⟨P.composition_target, P.composition_source⟩

/-- Any morphism with the target/source equations of `P.composition` is equal to
`P.composition`. -/
theorem eq_composition_of_target_source {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] {c : pullback P.s P.t ⟶ P.left}
    (hc_t : c ≫ P.t = pullback.fst P.s P.t ≫ P.t)
    (hc_s : c ≫ P.s = pullback.snd P.s P.t ≫ P.s) :
    c = P.composition := by
  exact (inferInstance : JointlyMono₂ P.t P.s).right_cancellation c P.composition
    (hc_t.trans P.composition_target.symm) (hc_s.trans P.composition_source.symm)

/-- An internal equivalence relation over a scheme has a unique composition on composable arrows,
characterized by its target and source. -/
theorem existsUniqueComposition {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] :
    ∃! c : pullback P.s P.t ⟶ P.left,
      c ≫ P.t = pullback.fst P.s P.t ≫ P.t ∧
        c ≫ P.s = pullback.snd P.s P.t ≫ P.s := by
  refine ⟨P.composition, P.composition_spec, ?_⟩
  intro c hc
  exact P.eq_composition_of_target_source hc.1 hc.2

end AlgebraicGeometry.Scheme.PreRelation
