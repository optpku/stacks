/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.CanonicalComparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Trace
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/-- The projection-formula map from absolute forms tensored with the pushed-forward structure
module to pushed-forward absolute forms. -/
noncomputable def pushforwardFormMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) (p : ℕ) :
    (Λ[p] Ω[(terminal.from X).toShHom]) ⊗ f.pushforwardStructureModule ⟶
      (Scheme.Modules.pushforward f).obj
        (Λ[p] Ω[(terminal.from Y).toShHom]) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).projectionFormulaMateOfIso
      (Scheme.Modules.pullbackTensorIso f)
      (Λ[p] Ω[(terminal.from X).toShHom])
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≫
    (Scheme.Modules.pushforward f).map
      ((absoluteFormComparison f p ⊗ₘ
          RingedSpace.unitModuleToTensorUnit Y.toRingedSpace) ≫
        (ρ_ (Λ[p] Ω[(terminal.from Y).toShHom])).hom)

/-- The named projection-formula comparison is the canonical mate followed by the absolute-form
comparison and the tensor-unit map. -/
theorem pushforwardFormMap_def
    {X Y : Scheme.{u}} (f : Y ⟶ X) (p : ℕ) :
    pushforwardFormMap f p =
      (Scheme.Modules.pullbackPushforwardAdjunction f).projectionFormulaMateOfIso
          (Scheme.Modules.pullbackTensorIso f)
          (Λ[p] Ω[(terminal.from X).toShHom])
          (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≫
        (Scheme.Modules.pushforward f).map
          ((absoluteFormComparison f p ⊗ₘ
              RingedSpace.unitModuleToTensorUnit Y.toRingedSpace) ≫
            (ρ_ (Λ[p] Ω[(terminal.from Y).toShHom])).hom) := sorry

/-- A degreewise trace rule assigns a map from pushed-forward absolute forms to absolute forms
for every finite syntomic morphism. -/
structure TraceRule where
  /-- The trace map assigned to a finite syntomic morphism in degree `p`. -/
  component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Syntomic f] (p : ℕ),
      (Scheme.Modules.pushforward f).obj
          (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
        Λ[p] Ω[(terminal.from X).toShHom]

namespace TraceRule

/-- Construct a trace rule from its complete family of components. -/
def ofComponents
    (component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsFinite f] [Syntomic f] (p : ℕ),
        (Scheme.Modules.pushforward f).obj
            (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
          Λ[p] Ω[(terminal.from X).toShHom]) : TraceRule.{u} :=
  ⟨component⟩

/-- Evaluation of a trace rule built from components recovers the supplied component. -/
theorem ofComponents_apply
    (component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsFinite f] [Syntomic f] (p : ℕ),
        (Scheme.Modules.pushforward f).obj
            (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
          Λ[p] Ω[(terminal.from X).toShHom])
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] (p : ℕ) :
    (ofComponents component).component f p = component f p := sorry

/-- Two trace rules are equal when all of their components agree. -/
theorem ext (r₁ r₂ : TraceRule.{u})
    (h : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsFinite f] [Syntomic f] (p : ℕ),
        r₁.component f p = r₂.component f p) :
    r₁ = r₂ := sorry

end TraceRule

/-- The projection-formula normalization and arbitrary cartesian base-change laws for a
degreewise trace rule. -/
structure IsTraceRule
    (r : TraceRule.{u}) : Prop where
  /-- Precomposing a trace component with the projection-formula comparison is tensoring the
  structure-sheaf trace with the identity on absolute forms. -/
  normalization : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Syntomic f] (p : ℕ),
      pushforwardFormMap f p ≫ r.component f p =
        (𝟙 (Λ[p] Ω[(terminal.from X).toShHom]) ⊗ₘ
          (Scheme.Hom.finiteSyntomicTrace f ≫
            RingedSpace.unitModuleToTensorUnit X.toRingedSpace)) ≫
          (ρ_ (Λ[p] Ω[(terminal.from X).toShHom])).hom
  /-- Trace components commute with the canonical comparison maps in every cartesian
  base-change square. -/
  baseChange : ∀ {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : IsPullback b f' f a) [IsFinite f] [Syntomic f]
    [IsFinite f'] [Syntomic f'] (p : ℕ),
      (Scheme.Modules.fromRingedSpace X').map
          ((RingedSpace.Hom.BaseChange.map
            (sq.toCommSq.map
              (Scheme.forgetToLocallyRingedSpace ⋙
                LocallyRingedSpace.forgetToSheafedSpace))).app
              (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
          (Scheme.Modules.pushforward f').map (absoluteFormComparison b p) ≫
          r.component f' p =
        (Scheme.Modules.pullback a).map (r.component f p) ≫
          absoluteFormComparison a p

namespace IsTraceRule

/-- Assemble the normalization and cartesian base-change properties of a trace rule. -/
def ofProperties (r : TraceRule.{u})
    (normalization : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsFinite f] [Syntomic f] (p : ℕ),
        pushforwardFormMap f p ≫ r.component f p =
          (𝟙 (Λ[p] Ω[(terminal.from X).toShHom]) ⊗ₘ
            (Scheme.Hom.finiteSyntomicTrace f ≫
              RingedSpace.unitModuleToTensorUnit X.toRingedSpace)) ≫
            (ρ_ (Λ[p] Ω[(terminal.from X).toShHom])).hom)
    (baseChange : ∀ {X' X Y' Y : Scheme.{u}}
      (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
      (sq : IsPullback b f' f a) [IsFinite f] [Syntomic f]
      [IsFinite f'] [Syntomic f'] (p : ℕ),
        (Scheme.Modules.fromRingedSpace X').map
            ((RingedSpace.Hom.BaseChange.map
              (sq.toCommSq.map
                (Scheme.forgetToLocallyRingedSpace ⋙
                  LocallyRingedSpace.forgetToSheafedSpace))).app
                (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
            (Scheme.Modules.pushforward f').map (absoluteFormComparison b p) ≫
            r.component f' p =
          (Scheme.Modules.pullback a).map (r.component f p) ≫
            absoluteFormComparison a p) :
    IsTraceRule r :=
  ⟨normalization, baseChange⟩

/-- A valid trace rule satisfies its normalization and base-change laws together. -/
theorem spec {r : TraceRule.{u}} (hr : IsTraceRule r) :
    (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsFinite f] [Syntomic f] (p : ℕ),
        pushforwardFormMap f p ≫ r.component f p =
          (𝟙 (Λ[p] Ω[(terminal.from X).toShHom]) ⊗ₘ
            (Scheme.Hom.finiteSyntomicTrace f ≫
              RingedSpace.unitModuleToTensorUnit X.toRingedSpace)) ≫
            (ρ_ (Λ[p] Ω[(terminal.from X).toShHom])).hom) ∧
      (∀ {X' X Y' Y : Scheme.{u}}
        (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
        (sq : IsPullback b f' f a) [IsFinite f] [Syntomic f]
        [IsFinite f'] [Syntomic f'] (p : ℕ),
          (Scheme.Modules.fromRingedSpace X').map
              ((RingedSpace.Hom.BaseChange.map
                (sq.toCommSq.map
                  (Scheme.forgetToLocallyRingedSpace ⋙
                    LocallyRingedSpace.forgetToSheafedSpace))).app
                  (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
              (Scheme.Modules.pushforward f').map (absoluteFormComparison b p) ≫
              r.component f' p =
            (Scheme.Modules.pullback a).map (r.component f p) ≫
              absoluteFormComparison a p) := sorry

end IsTraceRule

/-- Every finite syntomic morphism admits a unique trace rule satisfying normalization and
cartesian base-change compatibility. -/
theorem existsUniqueTraceRule :
    ∃! r : TraceRule.{u}, IsTraceRule r := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
