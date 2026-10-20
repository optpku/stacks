/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

/-- A surjective étale morphism to a quasi-compact and quasi-separated scheme admits a
surjective finite morphism of finite presentation which locally factors through the original
morphism. -/
theorem exists_surjective_finite_refinement {U X : Scheme.{u}} (f : U ⟶ X)
    [Surjective f] [Etale f] [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (h_surjective : Surjective p)
      (h_finite : IsFinite p)
      (h_finitePresentation : Scheme.Hom.FinitePresentation p),
      ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
        ∃ g : V.toScheme ⟶ U, g ≫ f = V.ι ≫ p := sorry

end AlgebraicGeometry.Etale
