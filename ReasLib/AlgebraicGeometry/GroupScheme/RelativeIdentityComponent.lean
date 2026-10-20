/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MonObj
open AlgebraicGeometry.Scheme.Hom.Section
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.GroupScheme

/-- The relative identity component of a group scheme, as the fibrewise
connected-component locus of the unit section. -/
noncomputable def identityComponentLocus {S : Scheme.{u}} (G : GroupScheme S) :
    Set G.X.left :=
  componentLocus G.X.hom (η[G.X]).left (Over.w (η[G.X]))

/-- The unit section lands in the relative identity-component locus. -/
theorem one_mem_identityComponentLocus {S : Scheme.{u}} (G : GroupScheme S) (s : S) :
    (η[G.X]).left s ∈ identityComponentLocus G := sorry

end AlgebraicGeometry.GroupScheme
