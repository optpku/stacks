/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsFinite

/-- A quasi-finite separated morphism of Noetherian schemes is finite when a coherent module
with full support has coherent pushforward and vanishing higher direct images in positive degrees. -/
theorem of_coherent_fullSupport
    {V X : Scheme.{u}} (f : V ⟶ X) [IsNoetherian V] [IsNoetherian X]
    [Scheme.Hom.QuasiFinite f] [IsSeparated f] (K : V.Modules) [K.IsCoherent]
    (h_support : Scheme.Modules.moduleSupport K = Set.univ)
    [((Scheme.Modules.pushforward f).obj K).IsCoherent]
    (hR : ∀ q : ℕ, 0 < q →
      IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom K q)) :
    IsFinite f := sorry

end AlgebraicGeometry.IsFinite
