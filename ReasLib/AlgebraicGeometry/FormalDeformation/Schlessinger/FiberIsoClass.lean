/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

/-!
# Schlessinger's second condition for fibrewise isomorphism classes

The fibrewise isomorphism-class functor of a predeformation category inherits
the set-valued form of Schlessinger's second condition.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The fibrewise isomorphism-class functor of a predeformation category satisfies (H2). -/
instance instHasSchlessingerH2FiberIsoClassFunctor
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] [HasSchlessingerS2 p] :
    HasSchlessingerH2 (fiberIsoClassFunctor p) := by
  sorry

end CategoryTheory.Functor
