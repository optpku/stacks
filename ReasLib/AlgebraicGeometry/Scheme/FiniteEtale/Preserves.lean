/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import ReasLib.CategoryTheory.Limits.Over.FiniteConnected
public import Mathlib.CategoryTheory.Limits.MorphismProperty

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The forgetful functor from finite étale schemes over `X` to `Over X`. -/
abbrev toOver (X : Scheme.{u}) : FiniteEtale X ⥤ CategoryTheory.Over X :=
  MorphismProperty.Over.forget finiteEtaleMorphism (⊤ : MorphismProperty Scheme.{u}) X

/-- The composite of `toOver X` with the slice forgetful functor to schemes. -/
abbrev toScheme (X : Scheme.{u}) : FiniteEtale X ⥤ Scheme :=
  toOver X ⋙ CategoryTheory.Over.forget X

/-- The functor `toScheme X` preserves finite colimits. -/
instance toScheme_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (toScheme X) := sorry

/-- The functor `toOver X` preserves finite colimits. -/
instance toOver_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (toOver X) := sorry

/-- The functor `toOver X` preserves finite limits. -/
instance toOver_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (toOver X) := sorry

/-- The functor `toScheme X` preserves finite connected limits. -/
instance toScheme_preservesFiniteConnectedLimits (X : Scheme.{u}) :
    PreservesFiniteConnectedLimits (toScheme X) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
