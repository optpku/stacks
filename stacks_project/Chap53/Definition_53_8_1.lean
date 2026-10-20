/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap53.Definition_53_8_1_Genus
import StacksCheckRecall

universe u

/- Definition 53.8.1: the genus of a proper one-dimensional scheme `X` over a field `k`
whose canonical map `k → Γ(X, 𝒪_X)` is bijective is `dim_k H¹(X, 𝒪_X)`. -/
@[stacks 0BY7] #check (AlgebraicGeometry.SchemeOverField.genus : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom],
  (topologicalKrullDim X.left = 1) →
  Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom) → ℕ)

#check AlgebraicGeometry.SchemeOverField.genus_def
