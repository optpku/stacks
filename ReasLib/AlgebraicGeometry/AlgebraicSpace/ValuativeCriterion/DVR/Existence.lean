/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.FiniteSeparable

/-!
# DVR existence after dominating extensions

A morphism of algebraic spaces may satisfy existence in the valuative criterion
after replacing a discrete valuation ring by a dominating valuation ring, or by
a finite separable discrete valuation ring extension.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A dotted lift gives the identity dominating extension, with unchanged ring and field. -/
private theorem exists_identityExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : ValuativeCommSq f) (l : sq.commSq.LiftStruct)
    (hR : IsDiscreteValuationRing sq.R) :
    ∃ e : sq.Extension,
      FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' ∧
        IsDiscreteValuationRing e.R' := by
  letI : IsExtensionOfValuationRings sq.R sq.R := {
    toIsLocalHom := isLocalHom_id sq.R
    algebraMap_injective := Function.injective_id }
  let liftHom :
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.R)) ≫
        sq.structureHom)) ⟶ X :=
    ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.R))) rfl ≫ l.l
  have fac_left :
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl ≫ liftHom =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K sq.K)))
          (ValuativeCommSq.Extension.specK_compat_of sq sq.R sq.K) ≫ sq.i₁ := by
    have hcomp :
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl ≫
            ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.R))) rfl =
          ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K sq.K)))
            (ValuativeCommSq.Extension.specK_compat_of sq sq.R sq.K) ≫ sq.verticalMap := by
      change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Over.OverMorphism.ext
      simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
        Over.comp_left, Over.homMk_left]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    dsimp only [liftHom]
    calc
      _ = (_ ≫ _) ≫ l.l := (Category.assoc _ _ _).symm
      _ = (_ ≫ sq.verticalMap) ≫ l.l := congrArg (fun a ↦ a ≫ l.l) hcomp
      _ = _ ≫ (sq.verticalMap ≫ l.l) := Category.assoc _ _ _
      _ = _ := congrArg (fun a ↦ ofOverHomMk
        (Spec.map (CommRingCat.ofHom (algebraMap sq.K sq.K)))
        (ValuativeCommSq.Extension.specK_compat_of sq sq.R sq.K) ≫ a) l.fac_left
  have fac_right :
      liftHom ≫ f =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.R))) rfl ≫ sq.i₂ := by
    dsimp only [liftHom]
    rw [Category.assoc, l.fac_right]
  refine ⟨ValuativeCommSq.Extension.of sq sq.R sq.K liftHom fac_left fac_right, ?_, ?_, hR⟩
  · change FiniteDimensional sq.K sq.K
    infer_instance
  · change Algebra.IsSeparable sq.K sq.K
    infer_instance

/-- A morphism of algebraic spaces satisfies existence of a dominating
valuation-ring extension with a lift on every valuative square whose ring is a
discrete valuation ring. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExistsExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square admits a dominating valuation-ring extension with a
  lift. -/
  nonempty_extension :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension

namespace ValuativeCriterion.DVR.ExistsExtension

/-- The identity morphism of an algebraic space satisfies DVR existence after a
dominating extension. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : ExistsExtension (𝟙 X) where
  nonempty_extension sq hR := by
    obtain ⟨e, _⟩ := exists_identityExtension sq
      { l := sq.i₂
        fac_left := by simpa using sq.commSq.w.symm
        fac_right := Category.comp_id _ } hR
    exact ⟨e⟩

/-- Existence for all valuative squares implies existence after a dominating
extension on DVR valuative squares. -/
instance of_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Existence f] : ExistsExtension f where
  nonempty_extension sq _ := ValuativeCriterion.Existence.nonempty_extension sq

/-- A dotted lift on every DVR valuative square implies existence after a
dominating extension. -/
instance of_dvrExistence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f] : ExistsExtension f where
  nonempty_extension sq hR := by
    obtain ⟨l⟩ := ValuativeCriterion.DVR.Existence.nonempty_liftStruct sq hR
    obtain ⟨e, _⟩ := exists_identityExtension sq l hR
    exact ⟨e⟩

/-- A morphism satisfies DVR existence after a dominating extension if and only if
every DVR valuative square admits such an extension. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ExistsExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension :=
  ⟨fun h ↦ h.nonempty_extension, fun h ↦ ⟨h⟩⟩

/-- Under `ExistsExtension f`, every DVR valuative square admits a dominating
valuation-ring extension with a lift. -/
theorem exists_extension {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [ExistsExtension f] (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R) :
    Nonempty sq.Extension :=
  ExistsExtension.nonempty_extension sq hR

end ValuativeCriterion.DVR.ExistsExtension

/-- A morphism of algebraic spaces satisfies existence of a finite separable
dominating discrete valuation ring extension with a lift on every valuative
square whose ring is a discrete valuation ring. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExistsFiniteSeparableExtension
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square admits a finite separable field extension, a
  dominating discrete valuation ring, and a lift of the extended square. -/
  exists_finiteSeparable :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      ∃ e : sq.Extension,
        FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' ∧
          IsDiscreteValuationRing e.R'

namespace ValuativeCriterion.DVR.ExistsFiniteSeparableExtension

/-- The identity morphism of an algebraic space satisfies finite-separable DVR
existence after a dominating extension. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    ExistsFiniteSeparableExtension (𝟙 X) where
  exists_finiteSeparable sq hR :=
    exists_identityExtension sq
      { l := sq.i₂
        fac_left := by simpa using sq.commSq.w.symm
        fac_right := Category.comp_id _ } hR

/-- Existence for all valuative squares implies finite-separable DVR existence
after a dominating extension. -/
instance of_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Existence f] : ExistsFiniteSeparableExtension f := sorry

/-- A dotted lift on every DVR valuative square implies finite-separable DVR
existence after a dominating extension. -/
instance of_dvrExistence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f] : ExistsFiniteSeparableExtension f where
  exists_finiteSeparable sq hR := by
    obtain ⟨l⟩ := ValuativeCriterion.DVR.Existence.nonempty_liftStruct sq hR
    exact exists_identityExtension sq l hR

/-- A morphism satisfies finite-separable DVR existence after a dominating
extension if and only if every DVR valuative square admits a finite separable
dominating discrete valuation ring extension with a lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ExistsFiniteSeparableExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        ∃ e : sq.Extension,
          FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' ∧
            IsDiscreteValuationRing e.R' :=
  ⟨fun h ↦ h.exists_finiteSeparable, fun h ↦ ⟨h⟩⟩

end ValuativeCriterion.DVR.ExistsFiniteSeparableExtension

namespace ValuativeCriterion.DVR.ExistsExtension

/-- Finite-separable DVR existence after extension implies existence of some
dominating valuation-ring extension on DVR valuative squares. -/
instance of_existsFiniteSeparableExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [ExistsFiniteSeparableExtension f] : ExistsExtension f where
  nonempty_extension sq hR := by
    obtain ⟨e, _⟩ := ExistsFiniteSeparableExtension.exists_finiteSeparable sq hR
    exact ⟨e⟩

end ValuativeCriterion.DVR.ExistsExtension

end AlgebraicGeometry.AlgebraicSpace
