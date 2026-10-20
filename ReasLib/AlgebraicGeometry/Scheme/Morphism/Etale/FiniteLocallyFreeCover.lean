/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

/-- A surjective étale morphism between affine schemes is locally dominated by a surjective
finite locally free morphism whose source has a finite open cover factoring through the étale
morphism. -/
theorem exists_finiteLocallyFreeCover {U S : Scheme.{u}} (f : U ⟶ S)
    [IsAffine U] [IsAffine S] [Surjective f] [Etale f] :
    ∃ (T : Scheme.{u}) (π : T ⟶ S) (_ : Surjective π) (_ : IsFiniteLocallyFree π)
      (n : ℕ) (V : Fin n → T.Opens),
      TopologicalSpace.IsOpenCover V ∧
        ∀ i, ∃ g : (V i).toScheme ⟶ U, g ≫ f = (V i).ι ≫ π := sorry

end AlgebraicGeometry.Etale
