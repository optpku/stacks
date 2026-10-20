/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Localization
import StacksCheckRecall

/-!
# Localization of ring deformation categories
-/

@[expose] public section

open CategoryTheory

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]

/- Lemma 93.8.7: in Example 93.8.1, a `k`-algebra `P` and a multiplicative subset
`S ⊆ P` induce a natural functor
`deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S)`
of deformation categories, preserving their Artinian local bases. -/
@[stacks 0DYS] #check (FlatAlgebraCat.localizationFunctor :
  ∀ (S : Submonoid P),
    FlatAlgebraCat.deformationCategory Λ k P ⥤
      FlatAlgebraCat.deformationCategory Λ k (Localization S))
