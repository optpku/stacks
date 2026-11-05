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

/-- The point of the restricted presentation at the `n`th truncation. -/
def coyonedaTruncatedPoint (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) :
    (ofFormalObject ξ).U.obj (p.base.truncation n) :=
  ε.hom.obj.app (p.base.truncation n)
    ((ofCoyoneda s t c idMap invMap laws).U.map (FormalObject.restrictedIdentity p.base n).2 p.fiber)

/-- The restricted identity arrow giving the successor transition between truncations. -/
def coyonedaTruncatedStepArrow (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) :
    (ofFormalObject ξ).R.obj (p.base.truncation n) :=
  ε.hom.arrow.app (p.base.truncation n)
    ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity p.base n).2
      ((ofCoyoneda s t c idMap invMap laws).e.app p.base p.fiber))

/-- A quotient arrow restricted to the `n`th truncation of its target. -/
def coyonedaTruncatedMapArrow {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) :
    (ofFormalObject ξ).R.obj (q.base.truncation n) :=
  ε.hom.arrow.app (q.base.truncation n)
    ((ofCoyoneda s t c idMap invMap laws).R.map (FormalObject.restrictedIdentity q.base n).2 φ.fiber.arrow)

/-- Truncating quotient arrows and applying a restricted presentation preserves their endpoints. -/
theorem coyonedaQuotientMap_stage_laws :
    (∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ),
      (ofFormalObject ξ).s.app (p.base.truncation n) (coyonedaTruncatedStepArrow ξ ε p n) =
        (ofFormalObject ξ).U.map (p.base.truncationMap n) (coyonedaTruncatedPoint ξ ε p (n + 1)) ∧
      (ofFormalObject ξ).t.app (p.base.truncation n) (coyonedaTruncatedStepArrow ξ ε p n) =
        coyonedaTruncatedPoint ξ ε p n) ∧
    (∀ (p q : (ofCoyoneda s t c idMap invMap laws).quotient.total) (φ : p ⟶ q) (n : ℕ),
      (ofFormalObject ξ).s.app (q.base.truncation n) (coyonedaTruncatedMapArrow ξ ε φ n) =
        (ofFormalObject ξ).U.map (truncationHom φ.base n) (coyonedaTruncatedPoint ξ ε p n) ∧
      (ofFormalObject ξ).t.app (q.base.truncation n) (coyonedaTruncatedMapArrow ξ ε φ n) =
        coyonedaTruncatedPoint ξ ε q n) := sorry

/-- The canonical kernel-pair quotient image of a truncated presentation point. -/
def coyonedaComparisonStage :
  (ofCoyoneda s t c idMap invMap laws).quotient.total → ℕ → ULiftHom.{u + 1} F.total :=
  fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
    ULiftHom.objUp ((quotientMap (FormalObject.associatedMorphismOver ξ)).obj
    ((ofFormalObject ξ).quotientObj (p.base.truncation n) (coyonedaTruncatedPoint ξ ε p n)))

/-- The canonical quotient image of the restricted successor arrow. -/
def coyonedaComparisonStep :
  ∀ (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ), coyonedaComparisonStage ξ ε p (n + 1) ⟶ coyonedaComparisonStage ξ ε p n :=
  fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) ↦
    ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
    (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (p.base.truncationMap n)
      (PointHom.ofArrow (coyonedaTruncatedStepArrow ξ ε p n)
        ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).1
        ((coyonedaQuotientMap_stage_laws ξ ε).1 p n).2)))

/-- The comparison stages and successor maps lie over the maximal-adic truncation tower. -/
theorem coyonedaQuotientMap_obj_laws (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) :
    (∀ n, (ULiftHom.down ⋙ F.p).obj (coyonedaComparisonStage ξ ε p n) = p.base.truncation n) ∧
    (∀ n, (ULiftHom.down ⋙ F.p).IsHomLift (p.base.truncationMap n)
      (coyonedaComparisonStep ξ ε p n)) := sorry

/-- The canonical quotient image of a truncated quotient arrow. -/
def coyonedaComparisonStageMap :
  ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → ∀ (n : ℕ), coyonedaComparisonStage ξ ε p n ⟶ coyonedaComparisonStage ξ ε q n :=
  fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) ↦
    ULiftHom.up.map ((quotientMap (FormalObject.associatedMorphismOver ξ)).map
    (Functor.ofGroupoidValued.mkHom (ofFormalObject ξ).toFunctor (truncationHom φ.base n)
      (PointHom.ofArrow (coyonedaTruncatedMapArrow ξ ε φ n)
        ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).1
        ((coyonedaQuotientMap_stage_laws ξ ε).2 p q φ n).2)))

/-- The formal object assembled from the canonical comparison stages and transitions. -/
def coyonedaComparisonObject :
  (ofCoyoneda s t c idMap invMap laws).quotient.total → FormalObject (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) :=
  fun (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) ↦
    FormalObject.of p.base (coyonedaComparisonStage ξ ε p) (coyonedaComparisonStep ξ ε p)
    (coyonedaQuotientMap_obj_laws ξ ε p).1 (coyonedaQuotientMap_obj_laws ξ ε p).2

/-- The truncated comparison arrows lift the truncated base map and commute with transitions. -/
theorem coyonedaQuotientMap_map_laws {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) :
    (∀ n, (ULiftHom.down ⋙ F.p).IsHomLift (truncationHom φ.base n)
      (coyonedaComparisonStageMap ξ ε φ n)) ∧
    (∀ n, (coyonedaComparisonObject ξ ε p).system.stepMap n ≫ coyonedaComparisonStageMap ξ ε φ n =
      coyonedaComparisonStageMap ξ ε φ (n + 1) ≫ (coyonedaComparisonObject ξ ε q).system.stepMap n) := sorry

/-- The formal morphism with the supplied base map and canonical comparison stage maps. -/
def coyonedaComparisonMap :
  ∀ {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total}, (p ⟶ q) → (coyonedaComparisonObject ξ ε p ⟶ coyonedaComparisonObject ξ ε q) :=
  fun {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) ↦
    FormalObject.Hom.of φ.base (coyonedaComparisonStageMap ξ ε φ)
    (fun n ↦ truncationHom φ.base n)
    (coyonedaQuotientMap_map_laws ξ ε φ).1
    (fun n ↦ truncationHom_spec φ.base n)
    (coyonedaQuotientMap_map_laws ξ ε φ).2

/-- The comparison formal object retains the original complete local base. -/
theorem coyonedaComparisonObject_base
    (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) :
    (coyonedaComparisonObject ξ ε p).base = p.base := rfl

/-- The comparison formal object's stages are the canonical quotient images. -/
theorem coyonedaComparisonObject_family
    (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) (n : ℕ) :
    (coyonedaComparisonObject ξ ε p).system.family n = coyonedaComparisonStage ξ ε p n := rfl

/-- The comparison formal morphism retains the original base map. -/
theorem coyonedaComparisonMap_base
    {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) :
    (coyonedaComparisonMap ξ ε φ).base = φ.base := rfl

/-- The comparison formal morphism has the canonical quotient images as its stage maps. -/
theorem coyonedaComparisonMap_app
    {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) :
    (coyonedaComparisonMap ξ ε φ).app n = coyonedaComparisonStageMap ξ ε φ n := rfl

/-- The comparison formal morphism uses the canonical truncations of the base map. -/
theorem coyonedaComparisonMap_baseTrunc
    {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) (n : ℕ) :
    (coyonedaComparisonMap ξ ε φ).baseTrunc n = truncationHom φ.base n := rfl

/-- Stagewise comparison maps preserve identities and composition of quotient arrows. -/
theorem coyonedaQuotientMap_functor_laws :
    (∀ p : (ofCoyoneda s t c idMap invMap laws).quotient.total,
      coyonedaComparisonMap ξ ε (𝟙 p) = 𝟙 (coyonedaComparisonObject ξ ε p)) ∧
    (∀ (p q r : (ofCoyoneda s t c idMap invMap laws).quotient.total) (φ : p ⟶ q) (ψ : q ⟶ r),
      coyonedaComparisonMap ξ ε (φ ≫ ψ) = coyonedaComparisonMap ξ ε φ ≫ coyonedaComparisonMap ξ ε ψ) := sorry

/-- The canonical completed comparison evaluates the restricted presentation on each truncation,
then applies the kernel-pair quotient map of the formal object. -/
def coyonedaQuotientMap :
    (ofCoyoneda s t c idMap invMap laws).quotient.toBasedCategory ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion
        (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k)) :=
  let comparisonFunctor : (ofCoyoneda s t c idMap invMap laws).quotient.total ⥤
      FormalObject (ULiftHom.down ⋙ F.p : ULiftHom.{u + 1} F.total ⥤ ArtinianLocalAlgCat Λ k) :=
    { obj := coyonedaComparisonObject ξ ε
      map := coyonedaComparisonMap ξ ε
      map_id := (coyonedaQuotientMap_functor_laws ξ ε).1
      map_comp := fun φ ψ ↦ (coyonedaQuotientMap_functor_laws ξ ε).2 _ _ _ φ ψ }
  BasedFunctor.ofFunctor comparisonFunctor rfl

/-- The completed comparison assembles the comparison formal objects. -/
theorem coyonedaQuotientMap_obj
    (p : (ofCoyoneda s t c idMap invMap laws).quotient.total) :
    (coyonedaQuotientMap ξ ε).obj p = coyonedaComparisonObject ξ ε p := rfl

/-- The completed comparison assembles the comparison formal morphisms. -/
theorem coyonedaQuotientMap_map
    {p q : (ofCoyoneda s t c idMap invMap laws).quotient.total} (φ : p ⟶ q) :
    (coyonedaQuotientMap ξ ε).map φ = coyonedaComparisonMap ξ ε φ := rfl

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
