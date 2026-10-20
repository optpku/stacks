/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative.Uniqueness
import StacksCheckRecall

universe u

open scoped TensorProduct

/- Lemma 47.27.2: any two relative dualizing complexes for a flat finitely presented
commutative algebra `A` over `R` are isomorphic in `DerivedCategory (ModuleCat A)`. -/
@[stacks 0E2D] #check
  (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.isomorphic :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.Flat R A] [Algebra.FinitePresentation R A]
      [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A ⊗[R] A)]
      {K L : DerivedCategory (ModuleCat A)},
      CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R K →
        CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R L →
        CategoryTheory.IsIsomorphic K L)
