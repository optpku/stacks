/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative.Homothety

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory.InternalHom.RHom

noncomputable section

universe u

open scoped TensorProduct

/- Lemma 47.27.5 -/
@[stacks 0E2G] #check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.homothety_isIso :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.Flat R A] [Algebra.FinitePresentation R A]
      [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A ⊗[R] A)]
      [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A)]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u, u} A))]
      {K : DerivedCategory (ModuleCat.{u, u} A)},
      CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R K →
      (M : ClosedComparison) →
      (s : Unit.single ≅ 𝟙_ (DerivedCategory (ModuleCat.{u, u} A))) →
      IsIso (s.hom ≫
        @MonoidalClosed.curry' (DerivedCategory (ModuleCat.{u, u} A)) _ _
          K K (M.closed.closed K) (𝟙 K) ≫
        (M.objIso K K).inv))
