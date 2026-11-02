/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExtensionDense

/-!
# Complete DVR valuative criteria for morphisms of algebraic spaces
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces satisfies the uniqueness part of the complete
DVR valuative criterion if every valuative commutative square whose ring is a
complete discrete valuation ring has at most one lift. -/
class ValuativeCriterion.CompleteDVR.Uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every complete DVR valuative square has at most one dotted lift. -/
  subsingleton_liftStruct :
    ∀ sq : ValuativeCommSq f,
      IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
        Subsingleton sq.commSq.LiftStruct

namespace ValuativeCriterion.CompleteDVR.Uniqueness

/-- The identity morphism of an algebraic space satisfies complete DVR uniqueness. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Uniqueness (𝟙 X) where
  subsingleton_liftStruct _ _ _ := inferInstance

/-- Uniqueness for all discrete valuation rings implies uniqueness for complete
discrete valuation rings. -/
instance of_dvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Uniqueness f] : Uniqueness f where
  subsingleton_liftStruct sq hR _ :=
    ValuativeCriterion.DVR.Uniqueness.subsingleton_liftStruct sq hR

/-- A morphism satisfies complete DVR uniqueness if and only if every complete
DVR valuative square has at most one lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Uniqueness f ↔
      ∀ sq : ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
          Subsingleton sq.commSq.LiftStruct :=
  ⟨fun h ↦ h.subsingleton_liftStruct, fun h ↦ ⟨h⟩⟩

end ValuativeCriterion.CompleteDVR.Uniqueness

/-- A morphism of algebraic spaces satisfies the existence part of the complete
DVR valuative criterion if every valuative commutative square whose ring is a
complete discrete valuation ring admits an extension `A ⊂ A'` of complete
discrete valuation rings together with a unique lift `Spec(A') ⟶ X`. -/
class ValuativeCriterion.CompleteDVR.Existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every complete DVR valuative square admits a complete DVR extension with a
  unique lift `Spec(A') ⟶ X` of the extended square. -/
  nonempty_extension :
    ∀ sq : ValuativeCommSq f,
      IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
        ∃ e : sq.Extension,
          IsDiscreteValuationRing e.R' ∧ IsCompleteLocalRing e.R' ∧
            Subsingleton e.outerCommSq.LiftStruct

namespace ValuativeCriterion.CompleteDVR.Existence

/-- The identity morphism of an algebraic space satisfies complete DVR existence. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Existence (𝟙 X) where
  nonempty_extension sq hR hC := by
    let e := ValuativeCommSq.Extension.of sq sq.R sq.K
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.R))) rfl ≫ sq.i₂)
      (by
        rw [show sq.i₁ = sq.verticalMap ≫ sq.i₂ by simpa using sq.commSq.w]
        simp only [← Category.assoc]
        apply congrArg (fun k ↦ k ≫ sq.i₂)
        change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Over.OverMorphism.ext
        change Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.R)) =
          Spec.map (CommRingCat.ofHom (algebraMap sq.K sq.K)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
        simp)
      (by simp)
    exact ⟨e, hR, hC, inferInstance⟩

/-- A morphism satisfies complete DVR existence if and only if every complete
DVR valuative square admits a complete DVR extension with a unique lift
`Spec(A') ⟶ X`. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔
      ∀ sq : ValuativeCommSq f,
        IsDiscreteValuationRing sq.R → IsCompleteLocalRing sq.R →
          ∃ e : sq.Extension,
            IsDiscreteValuationRing e.R' ∧ IsCompleteLocalRing e.R' ∧
              Subsingleton e.outerCommSq.LiftStruct :=
  ⟨fun h ↦ h.nonempty_extension, fun h ↦ ⟨h⟩⟩

end ValuativeCriterion.CompleteDVR.Existence

/-- A morphism of algebraic spaces satisfies the complete DVR valuative criterion
if it satisfies both the uniqueness and existence parts. -/
class ValuativeCriterion.CompleteDVR {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop
    extends ValuativeCriterion.CompleteDVR.Uniqueness f,
      ValuativeCriterion.CompleteDVR.Existence f

namespace ValuativeCriterion.CompleteDVR

/-- The identity morphism of an algebraic space satisfies the complete DVR
valuative criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    ValuativeCriterion.CompleteDVR (𝟙 X) :=
  { toUniqueness := Uniqueness.id, toExistence := Existence.id }

/-- A morphism satisfies the complete DVR valuative criterion if and only if it
satisfies both the uniqueness and existence parts. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ValuativeCriterion.CompleteDVR f ↔ Uniqueness f ∧ Existence f :=
  ⟨fun h ↦ ⟨h.toUniqueness, h.toExistence⟩,
    fun h ↦ { toUniqueness := h.1, toExistence := h.2 }⟩

end ValuativeCriterion.CompleteDVR

namespace ValuativeCriterion.DVR.Uniqueness

/-- Complete DVR uniqueness implies uniqueness for all discrete valuation rings. -/
instance (priority := low) of_completeDVR {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.CompleteDVR.Uniqueness f] : Uniqueness f :=
  of_extensionDense (P := fun R _ _ _ ↦ IsCompleteLocalRing R) f
    (fun sq hR hC ↦
      ValuativeCriterion.CompleteDVR.Uniqueness.subsingleton_liftStruct sq hR hC)

end ValuativeCriterion.DVR.Uniqueness

namespace ValuativeCriterion.DVR.Existence

/-- After a separated morphism, complete DVR existence implies existence of a
lift on every DVR valuative square. -/
instance (priority := low) of_completeDVR {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [ValuativeCriterion.CompleteDVR.Existence f] : Existence f :=
  of_extensionDense (P := fun R _ _ _ ↦ IsCompleteLocalRing R) f
    (fun sq hR hC ↦ by
      obtain ⟨e, hR', hC', _⟩ :=
        ValuativeCriterion.CompleteDVR.Existence.nonempty_extension sq hR hC
      exact ⟨e, hR', hC'⟩)

end ValuativeCriterion.DVR.Existence

end AlgebraicGeometry.AlgebraicSpace
