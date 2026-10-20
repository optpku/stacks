/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.AssociatedMorphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.CategoryTheory.Groupoid.KernelPair.Quotient

/-! # Completed comparison maps for coyoneda presentations -/

@[expose] public section

open CategoryTheory CompleteLocalAlgCat Limits Opposite
open scoped BasedFunctor

noncomputable section

universe u

namespace CategoryTheory.GroupoidInFunctors

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
  {F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}
  (ξ : FormalObject (ULiftHom.down ⋙ F.p :
    ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k))
  {B : CompleteLocalAlgCat Λ k} {s t : ξ.base ⟶ B} [HasPushout s t]
  {c : B ⟶ pushout s t}
  {idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B)}
  {invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B)}
  {laws : CoyonedaGroupoidLaws s t c idMap invMap}
  (ε : Iso (restrictInclusion (ofCoyoneda s t c idMap invMap laws)) (ofFormalObject ξ))

/-- Truncating quotient arrows and applying a restricted presentation preserves their endpoints. -/
theorem coyonedaQuotientMap_stage_laws :
    let truncatedPoint :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.obj.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)
    let truncatedStepArrow :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.arrow.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity p.base n).2
          ((ofCoyoneda s t c idMap invMap laws).e.app p.base p.fiber))
    let truncatedMapArrow :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ε.hom.arrow.app (q.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity q.base n).2 φ.fiber.arrow)
    (∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ),
      (ofFormalObject ξ).s.app (p.base.truncation n) (truncatedStepArrow p n) =
        (ofFormalObject ξ).U.map (p.base.truncationMap n) (truncatedPoint p (n + 1)) ∧
      (ofFormalObject ξ).t.app (p.base.truncation n) (truncatedStepArrow p n) =
        truncatedPoint p n) ∧
    (∀ (p q : (ofCoyoneda s t c idMap invMap laws).quotient.total) (φ : p ⟶ q) (n : ℕ),
      (ofFormalObject ξ).s.app (q.base.truncation n) (truncatedMapArrow φ n) =
        (ofFormalObject ξ).U.map (truncationHom φ.base n) (truncatedPoint p n) ∧
      (ofFormalObject ξ).t.app (q.base.truncation n) (truncatedMapArrow φ n) =
        truncatedPoint q n) := sorry

/-- The comparison stages and successor maps lie over the maximal-adic truncation tower. -/
theorem coyonedaQuotientMap_obj_laws (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) :
    let truncatedPoint :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.obj.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)
    let truncatedStepArrow :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.arrow.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity p.base n).2
          ((ofCoyoneda s t c idMap invMap laws).e.app p.base p.fiber))
    let comparisonStage :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → ℕ → ULiftHom.{u + 1} F.total :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.objUp ((quotientMap (FormalObject.associatedMorphismOver ξ)).obj
        ((ofFormalObject ξ).quotientObj (p.base.truncation n) (truncatedPoint p n)))
    let comparisonStep :
      ∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ), comparisonStage p (n + 1) ⟶ comparisonStage p n :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (p.base.truncationMap n)
          (PointHom.ofArrow (truncatedStepArrow p n)
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).2)))
    (∀ n, (ULiftHom.down ⋙ F.p).obj (comparisonStage p n) = p.base.truncation n) ∧
    (∀ n, (ULiftHom.down ⋙ F.p).IsHomLift (p.base.truncationMap n)
      (comparisonStep p n)) := sorry

/-- The truncated comparison arrows lift the truncated base map and commute with transitions. -/
theorem coyonedaQuotientMap_map_laws {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) :
    let truncatedPoint :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.obj.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)
    let truncatedStepArrow :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.arrow.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity p.base n).2
          ((ofCoyoneda s t c idMap invMap laws).e.app p.base p.fiber))
    let truncatedMapArrow :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ε.hom.arrow.app (q.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity q.base n).2 φ.fiber.arrow)
    let comparisonStage :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → ℕ → ULiftHom.{u + 1} F.total :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.objUp ((quotientMap (FormalObject.associatedMorphismOver ξ)).obj
        ((ofFormalObject ξ).quotientObj (p.base.truncation n) (truncatedPoint p n)))
    let comparisonStep :
      ∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ), comparisonStage p (n + 1) ⟶ comparisonStage p n :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (p.base.truncationMap n)
          (PointHom.ofArrow (truncatedStepArrow p n)
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).2)))
    let comparisonStageMap :
      ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → ∀ (n : ℕ), comparisonStage p n ⟶ comparisonStage q n :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (truncationHom φ.base n)
          (PointHom.ofArrow (truncatedMapArrow φ n)
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).2)))
    let comparisonObject :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → FormalObject (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) ↦
        FormalObject.of p.base (comparisonStage p) (comparisonStep p)
        (coyonedaQuotientMap_obj_laws ξ ε p).1 (coyonedaQuotientMap_obj_laws ξ ε p).2
    (∀ n, (ULiftHom.down ⋙ F.p).IsHomLift (truncationHom φ.base n)
      (comparisonStageMap φ n)) ∧
    (∀ n, (comparisonObject p).system.stepMap n ≫ comparisonStageMap φ n =
      comparisonStageMap φ (n + 1) ≫ (comparisonObject q).system.stepMap n) := sorry

/-- Stagewise comparison maps preserve identities and composition of quotient arrows. -/
theorem coyonedaQuotientMap_functor_laws :
    let truncatedPoint :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.obj.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)
    let truncatedStepArrow :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.arrow.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity p.base n).2
          ((ofCoyoneda s t c idMap invMap laws).e.app p.base p.fiber))
    let truncatedMapArrow :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ε.hom.arrow.app (q.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity q.base n).2 φ.fiber.arrow)
    let comparisonStage :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → ℕ → ULiftHom.{u + 1} F.total :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.objUp ((quotientMap (FormalObject.associatedMorphismOver ξ)).obj
        ((ofFormalObject ξ).quotientObj (p.base.truncation n) (truncatedPoint p n)))
    let comparisonStep :
      ∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ), comparisonStage p (n + 1) ⟶ comparisonStage p n :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (p.base.truncationMap n)
          (PointHom.ofArrow (truncatedStepArrow p n)
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).2)))
    let comparisonStageMap :
      ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → ∀ (n : ℕ), comparisonStage p n ⟶ comparisonStage q n :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (truncationHom φ.base n)
          (PointHom.ofArrow (truncatedMapArrow φ n)
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).2)))
    let comparisonObject :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → FormalObject (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) ↦
        FormalObject.of p.base (comparisonStage p) (comparisonStep p)
        (coyonedaQuotientMap_obj_laws ξ ε p).1 (coyonedaQuotientMap_obj_laws ξ ε p).2
    let comparisonMap :
      ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → (comparisonObject p ⟶ comparisonObject q) :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) ↦
        FormalObject.Hom.of φ.base (comparisonStageMap φ)
        (fun n ↦ truncationHom φ.base n)
        (coyonedaQuotientMap_map_laws ξ ε φ).1
        (fun n ↦ truncationHom_spec φ.base n)
        (coyonedaQuotientMap_map_laws ξ ε φ).2
    (∀ p : (ofCoyoneda s t c idMap invMap laws).quotient.total,
      comparisonMap (𝟙 p) = 𝟙 (comparisonObject p)) ∧
    (∀ (p q r : (ofCoyoneda s t c idMap invMap laws).quotient.total) (φ : p ⟶ q) (ψ : q ⟶ r),
      comparisonMap (φ ≫ ψ) = comparisonMap φ ≫ comparisonMap ψ) := sorry

/-- The canonical completed comparison evaluates the restricted presentation on each truncation,
then applies the kernel-pair quotient map of the formal object. -/
def coyonedaQuotientMap :
    (ofCoyoneda s t c idMap invMap laws).quotient.toBasedCategory ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion
        (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k)) :=
    let truncatedPoint :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.obj.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)
    let truncatedStepArrow :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ε.hom.arrow.app (p.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity p.base n).2
          ((ofCoyoneda s t c idMap invMap laws).e.app p.base p.fiber))
    let truncatedMapArrow :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ε.hom.arrow.app (q.base.truncation n)
        ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity q.base n).2 φ.fiber.arrow)
    let comparisonStage :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → ℕ → ULiftHom.{u + 1} F.total :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.objUp ((quotientMap (FormalObject.associatedMorphismOver ξ)).obj
        ((ofFormalObject ξ).quotientObj (p.base.truncation n) (truncatedPoint p n)))
    let comparisonStep :
      ∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ), comparisonStage p (n + 1) ⟶ comparisonStage p n :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (p.base.truncationMap n)
          (PointHom.ofArrow (truncatedStepArrow p n)
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).2)))
    let comparisonStageMap :
      ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → ∀ (n : ℕ), comparisonStage p n ⟶ comparisonStage q n :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
        ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (truncationHom φ.base n)
          (PointHom.ofArrow (truncatedMapArrow φ n)
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).2)))
    let comparisonObject :
      (ofCoyoneda s t c idMap invMap laws).quotient.total → FormalObject (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) :=
      fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) ↦
        FormalObject.of p.base (comparisonStage p) (comparisonStep p)
        (coyonedaQuotientMap_obj_laws ξ ε p).1 (coyonedaQuotientMap_obj_laws ξ ε p).2
    let comparisonMap :
      ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → (comparisonObject p ⟶ comparisonObject q) :=
      fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) ↦
        FormalObject.Hom.of φ.base (comparisonStageMap φ)
        (fun n ↦ truncationHom φ.base n)
        (coyonedaQuotientMap_map_laws ξ ε φ).1
        (fun n ↦ truncationHom_spec φ.base n)
        (coyonedaQuotientMap_map_laws ξ ε φ).2
    let comparisonFunctor : (ofCoyoneda s t c idMap invMap laws).quotient.total ⥤
      FormalObject (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) :=
      {
    obj := comparisonObject
    map := comparisonMap
    map_id := (coyonedaQuotientMap_functor_laws ξ ε).1
    map_comp := fun φ ψ ↦ (coyonedaQuotientMap_functor_laws ξ ε).2 _ _ _ φ ψ
    }
    BasedFunctor.ofFunctor comparisonFunctor rfl

/-- The completed comparison preserves the complete local base exactly. -/
theorem coyonedaQuotientMap_p :
    (coyonedaQuotientMap ξ ε).toFunctor ⋙ Functor.completion
      (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) =
        (ofCoyoneda s t c idMap invMap laws).quotient.p := rfl

/-- A comparison object's stage is obtained by truncating its point and applying the canonical quotient map. -/
theorem coyonedaQuotientMap_obj_family (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) :
    ((coyonedaQuotientMap ξ ε).obj p).system.family n =
      ULiftHom.objUp ((quotientMap (FormalObject.associatedMorphismOver ξ)).obj
        ((ofFormalObject ξ).quotientObj (p.base.truncation n)
          (ε.hom.obj.app (p.base.truncation n)
            ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)))) := rfl

/-- Each comparison arrow is the lifted canonical quotient image of its truncated presentation arrow. -/
theorem coyonedaQuotientMap_map_app {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) :
    ((coyonedaQuotientMap ξ ε).map φ).app n =
      ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
        (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (truncationHom φ.base n)
          (PointHom.ofArrow
            (ε.hom.arrow.app (q.base.truncation n)
              ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity q.base n).2 φ.fiber.arrow))
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).1
            ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).2))) := rfl

end CategoryTheory.GroupoidInFunctors
