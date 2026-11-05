/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure.Groupoid.IdentityInverse
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Product

/-!
# Composition on reduced image closures

Over a perfect field, the composable-pair scheme of the reduced arrow-image closure is reduced.
Target composition lifts canonically to this closure and respects its source and target maps.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- Over a perfect field, the pullback of the restricted source and target maps is reduced. -/
theorem reducedImageClosureComposablePullback_isReduced
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) :
    IsReduced
      (Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s).left
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t).left : Scheme) := by
  let eU₂ : Spec (CommRingCat.of k) ≅ G₂.U.left :=
    eU.trans (eqToIso (congrArg Over.left hU))
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  let s' : (Scheme.Hom.reducedImageClosureOver f.arrow).left ⟶ G₂.U.left := (i ≫ G₂.s).left
  let t' : (Scheme.Hom.reducedImageClosureOver f.arrow).left ⟶ G₂.U.left := (i ≫ G₂.t).left
  let X : Over (Spec (CommRingCat.of k)) := Over.mk ((i ≫ G₂.s).left ≫ eU₂.inv)
  let Y : Over (Spec (CommRingCat.of k)) := Over.mk ((i ≫ G₂.t).left ≫ eU₂.inv)
  -- Local instance justification (proof-local temporary data): the pullback comparison
  -- requires the inverse of the specified isomorphism to be mono.
  let _ : Mono eU₂.inv := by infer_instance
  -- Local instance justification (proof-local temporary data): reducedness of the first
  -- factor is needed only for this perfect-field pullback argument.
  let _ :
      IsReduced X.left := by
    dsimp [X]
    change
      IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subscheme : Scheme)
    infer_instance
  -- Local instance justification (proof-local temporary data): reducedness of the second
  -- factor is needed only for this perfect-field pullback argument.
  let _ :
      IsReduced Y.left := by
    dsimp [Y]
    change
      IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subscheme : Scheme)
    infer_instance
  -- Local instance justification (proof-local temporary data): the comparison-isomorphism
  -- argument consumes reducedness of this auxiliary pullback.
  let _ : IsReduced (Limits.pullback X.hom Y.hom : Scheme) :=
    SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField X Y
  let ePull :=
    ((pullbackIsPullbackOfCompMono s' t' eU₂.inv).conePointUniqueUpToIso
      (limit.isLimit (cospan X.hom Y.hom))).symm
  -- The mono base-change comparison identifies the original pullback with the
  -- pullback over `Spec k`, so reducedness transports across that comparison isomorphism.
  exact CategoryTheory.ObjectProperty.prop_of_iso (IsReduced ·) ePull
    (SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField X Y)

/-- Over a perfect field, the reduced arrow-image closure's composable-pair scheme factors
through the reduced arrow-image closure under target composition. -/
theorem reducedImageClosureCompositionLift_condition
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)) ≤
      (reducedImageClosureComposition f).left.ker := by
  have hReduced :
      IsReduced
        (Limits.pullback
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s).left
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t).left : Scheme) :=
    reducedImageClosureComposablePullback_isReduced eU hU f
  let ePullback :=
    CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S)
      (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
      (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)
  -- Local instance justification (proof-local temporary data): the factorization criterion
  -- needs reducedness transported from the underlying scheme pullback.
  let _ :
      IsReduced
        (Limits.pullback
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)).left := by
    exact CategoryTheory.ObjectProperty.prop_of_iso (IsReduced ·) ePullback.symm hReduced
  -- Reducedness of the composable-pair source lets the factorization criterion
  -- reduce the claim to the already-proved set-theoretic range containment.
  rw [Scheme.IdealSheafData.le_ker_iff_range_subset,
    Scheme.IdealSheafData.support_vanishingIdeal]
  simpa [Scheme.Hom.range_reducedImageClosureιOver (f := f.arrow)] using
    reducedImageClosureComposition_range_subset eU hU f hf

/-- The canonical lift of restricted composition to the reduced arrow-image closure lies over
the base scheme. -/
theorem reducedImageClosureCompositionLift_over
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
          (reducedImageClosureComposition f).left
          (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom =
      (Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)).hom := by
  -- The composition lift remains over `S` because ambient composition is over `S`.
  calc
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        (reducedImageClosureComposition f).left
        (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom
      =
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
            (reducedImageClosureComposition f).left
            (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
          (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι ≫
          G₂.R.hom := by
            rfl
    _ = (reducedImageClosureComposition f).left ≫ G₂.R.hom := by
          have hLift :
              (Scheme.IdealSheafData.vanishingIdeal
                (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
                  (reducedImageClosureComposition f).left
                  (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
                (Scheme.IdealSheafData.vanishingIdeal
                  (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
              (reducedImageClosureComposition f).left :=
            Scheme.IdealSheafData.lift_subschemeι
              (Scheme.IdealSheafData.vanishingIdeal
                (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
              (reducedImageClosureComposition f).left
              (reducedImageClosureCompositionLift_condition eU hU f hf)
          simpa [Category.assoc] using congrArg (fun g ↦ g ≫ G₂.R.hom) hLift
    _ = (Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)).hom := by
          simpa [Category.assoc] using (Over.w (reducedImageClosureComposition f))

/-- Target composition, canonically restricted to composable arrows in the reduced
arrow-image closure. -/
noncomputable def reducedImageClosureCompositionLift
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ⟶
      Scheme.Hom.reducedImageClosureOver f.arrow :=
  Over.homMk
    ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        (reducedImageClosureComposition f).left
        (reducedImageClosureCompositionLift_condition eU hU f hf))
    (reducedImageClosureCompositionLift_over eU hU f hf)

/-- Restricted composition followed by the reduced-closure inclusion is target composition
on the corresponding composable arrows. -/
theorem reducedImageClosureCompositionLift_toArrows
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureCompositionLift eU hU f hf ≫
      Scheme.Hom.reducedImageClosureιOver f.arrow =
      reducedImageClosureComposition f := by
  apply Over.OverMorphism.ext
  -- Forgetting to schemes identifies the restricted composition with ambient composition.
  change
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        (reducedImageClosureComposition f).left
        (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
      (reducedImageClosureComposition f).left
  exact Scheme.IdealSheafData.lift_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
    (reducedImageClosureComposition f).left
    (reducedImageClosureCompositionLift_condition eU hU f hf)

/-- Pointwise restricted composition agrees with ambient target-groupoid composition after
postcomposing with the reduced-closure inclusion. -/
theorem reducedImageClosureCompose_eq
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow =
      G₂.compose (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
        (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
        (by simpa [Category.assoc] using h) := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  have hLift :
      pullback.lift a b h ≫
          pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
            (Category.comp_id _) (Category.comp_id _) =
        pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) := by
    apply pullback.hom_ext
    · calc
        pullback.lift a b h ≫
            pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
              (Category.comp_id _) (Category.comp_id _) ≫
            pullback.fst G₂.s G₂.t =
          pullback.lift a b h ≫ pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i := by
            exact congrArg
              (fun g ↦ pullback.lift a b h ≫ g)
              (pullback.lift_fst
                (pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (by
                  simpa [Category.assoc] using
                    (pullback.condition_assoc
                      (f := i ≫ G₂.s) (g := i ≫ G₂.t) (h := 𝟙 G₂.U))))
        _ = a ≫ i := by
              simpa [Category.assoc] using congrArg (fun g ↦ g ≫ i) (pullback.lift_fst a b h)
        _ = pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) ≫
              pullback.fst G₂.s G₂.t := by
              symm
              exact pullback.lift_fst (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h)
    · calc
        pullback.lift a b h ≫
            pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
              (Category.comp_id _) (Category.comp_id _) ≫
            pullback.snd G₂.s G₂.t =
          pullback.lift a b h ≫ pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i := by
            exact congrArg
              (fun g ↦ pullback.lift a b h ≫ g)
              (pullback.lift_snd
                (pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (by
                  simpa [Category.assoc] using
                    (pullback.condition_assoc
                      (f := i ≫ G₂.s) (g := i ≫ G₂.t) (h := 𝟙 G₂.U))))
        _ = b ≫ i := by
              simpa [Category.assoc] using congrArg (fun g ↦ g ≫ i) (pullback.lift_snd a b h)
        _ = pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) ≫
              pullback.snd G₂.s G₂.t := by
              symm
              exact pullback.lift_snd (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h)
  -- The two pullback lifts agree on both projections, so restricted composition
  -- becomes ordinary ambient composition after postcomposing with the inclusion.
  calc
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫ i =
      pullback.lift a b h ≫ reducedImageClosureComposition f := by
        simpa [Category.assoc] using
          congrArg (fun g ↦ pullback.lift a b h ≫ g)
            (reducedImageClosureCompositionLift_toArrows eU hU f hf)
    _ =
      pullback.lift a b h ≫
        pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
          (Category.comp_id _) (Category.comp_id _) ≫ G₂.c := by
          rfl
    _ =
      pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) ≫ G₂.c := by
          simpa [Category.assoc] using congrArg (fun g ↦ g ≫ G₂.c) hLift
    _ = G₂.compose (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) := rfl

/-- After postcomposing with the reduced-closure inclusion, restricted composition has the
source of the earlier arrow. -/
theorem reducedImageClosureCompose_source_eq
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s =
      b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s := by
  -- Once restricted composition is rewritten into ambient composition, the
  -- source formula is exactly the ambient `compose_source` law.
  calc
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s =
      G₂.compose
          (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (by simpa [Category.assoc] using h) ≫
        G₂.s := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.s)
              (reducedImageClosureCompose_eq eU hU f hf a b h)
    _ = b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s := by
          simpa [Category.assoc] using
            G₂.compose_source
              (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (by simpa [Category.assoc] using h)

/-- After postcomposing with the reduced-closure inclusion, restricted composition has the
target of the later arrow. -/
theorem reducedImageClosureCompose_target_eq
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t =
      a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t := by
  -- The target formula is the ambient `compose_target` law after the same
  -- inclusion-based normalization.
  calc
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t =
      G₂.compose
          (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (by simpa [Category.assoc] using h) ≫
        G₂.t := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.t)
              (reducedImageClosureCompose_eq eU hU f hf a b h)
    _ = a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t := by
          simpa [Category.assoc] using
            G₂.compose_target
              (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (by simpa [Category.assoc] using h)

/-- Equality into the reduced image closure can be checked after postcomposing with the
closed-subscheme inclusion. -/
theorem reducedImageClosureInclusion_cancel
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (f : Hom G₁ G₂)
    {T : Over S} {x y : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow}
    (h :
      x ≫ Scheme.Hom.reducedImageClosureιOver f.arrow =
        y ≫ Scheme.Hom.reducedImageClosureιOver f.arrow) :
    x = y := sorry

/-- The restricted composition map has the expected source map. -/
theorem reducedImageClosure_comp_source
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureCompositionLift eU hU f hf ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      pullback.snd
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  -- Collapse the self-lift of the pullback projections before applying the source formula.
  simpa [Category.assoc, i, pullback.lift_fst_snd (i ≫ G₂.s) (i ≫ G₂.t)] using
    reducedImageClosureCompose_source_eq eU hU f hf
      (a := pullback.fst (i ≫ G₂.s) (i ≫ G₂.t))
      (b := pullback.snd (i ≫ G₂.s) (i ≫ G₂.t))
      (h := pullback.condition (f := i ≫ G₂.s) (g := i ≫ G₂.t))

/-- The restricted composition map has the expected target map. -/
theorem reducedImageClosure_comp_target
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureCompositionLift eU hU f hf ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) =
      pullback.fst
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  -- Collapse the self-lift of the pullback projections before applying the target formula.
  simpa [Category.assoc, i, pullback.lift_fst_snd (i ≫ G₂.s) (i ≫ G₂.t)] using
    reducedImageClosureCompose_target_eq eU hU f hf
      (a := pullback.fst (i ≫ G₂.s) (i ≫ G₂.t))
      (b := pullback.snd (i ≫ G₂.s) (i ≫ G₂.t))
      (h := pullback.condition (f := i ≫ G₂.s) (g := i ≫ G₂.t))

end AlgebraicGeometry.GroupoidScheme.Hom
