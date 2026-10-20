/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

/-!
# Pullback of zero schemes over a base

This file bundles the canonical map from the zero scheme of a pulled-back section as a
morphism over the base scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical map between the zero schemes of a section and its pullback commutes
with their structure morphisms to the base. -/
theorem zeroSchemePullbackMap_over
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections) :
    zeroSchemePullbackMap f.left ℒ s (zeroIdealSheaf_sectionsPullback f.left ℒ s) ≫
        (zeroSchemeι ℒ s ≫ X.hom) =
      zeroSchemeι ((Modules.pullback f.left).obj ℒ)
          (Modules.sectionsPullback f.left ℒ s) ≫ X'.hom := sorry

/-- The canonical morphism over `S` from the zero scheme of the pulled-back section to
the zero scheme of the original section. -/
noncomputable def zeroSchemePullbackOverHom
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections) :
    Over.mk
        (zeroSchemeι ((Modules.pullback f.left).obj ℒ)
          (Modules.sectionsPullback f.left ℒ s) ≫ X'.hom) ⟶
      Over.mk (zeroSchemeι ℒ s ≫ X.hom) :=
  Over.homMk
    (zeroSchemePullbackMap f.left ℒ s (zeroIdealSheaf_sectionsPullback f.left ℒ s))
    (zeroSchemePullbackMap_over f ℒ s)

/-- The underlying scheme morphism of `zeroSchemePullbackOverHom` is the canonical
zero-scheme pullback map. -/
@[simp]
theorem zeroSchemePullbackOverHom_left
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections) :
    (zeroSchemePullbackOverHom f ℒ s).left =
      zeroSchemePullbackMap f.left ℒ s
        (zeroIdealSheaf_sectionsPullback f.left ℒ s) := sorry

/-- The canonical map between the zero schemes is proper when the original morphism is
proper. -/
instance zeroSchemePullbackOverHom_isProper
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X) [IsProper f.left]
    (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections) :
    IsProper (zeroSchemePullbackOverHom f ℒ s).left := sorry

/-- The canonical map from the zero scheme of a pulled-back section is flat whenever the
original morphism is flat. -/
theorem zeroSchemePullbackOverHom_flat
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X) [Flat f.left]
    (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections) :
    Flat (zeroSchemePullbackOverHom f ℒ s).left := sorry

/-- The canonical map from the zero scheme of a pulled-back section has the relative
dimension of the original morphism. -/
theorem zeroSchemePullbackOverHom_relativeDimension
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X) (r : ℕ)
    [Hom.RelativeDimension f.left r]
    (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections) :
    Hom.RelativeDimension (zeroSchemePullbackOverHom f ℒ s).left r := sorry

end AlgebraicGeometry.Scheme
