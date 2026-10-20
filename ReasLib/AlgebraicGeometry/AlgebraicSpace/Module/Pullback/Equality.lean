/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Equality transport for module pullback on algebraic spaces

Equal morphisms of algebraic spaces induce canonically isomorphic module pullback
functors, whose components are the corresponding equality morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Pullbacks of module sheaves along equal morphisms of algebraic spaces are
isomorphic. -/
noncomputable def pullbackCongr {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) :
    pullback f ≅ pullback g :=
  eqToIso (congrArg pullback h)

/-- The component of `pullbackCongr` at a module is the corresponding `eqToHom` of
objects. -/
theorem pullbackCongr_hom_app {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g)
    (ℱ : Y.Modules) :
    (pullbackCongr h).hom.app ℱ =
      eqToHom (congrArg (fun φ ↦ (pullback φ).obj ℱ) h) := sorry


end AlgebraicGeometry.AlgebraicSpace.Modules
