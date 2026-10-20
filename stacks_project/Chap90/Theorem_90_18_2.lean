/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable.Criterion
import StacksCheckRecall

open CategoryTheory

universe u

/- Theorem 90.18.2: a functor is prorepresentable if and only if it is a
 deformation functor, its tangent space is finite-dimensional, and its canonical
 derivation-to-tangent map is injective. -/
@[stacks 06JM] #check
  (CategoryTheory.Functor.isProrepresentable_iff_finiteDimensional_ofDerivation :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] (F : ArtinianLocalAlgCat Λ k ⥤ Type u),
      CategoryTheory.Functor.IsProrepresentable F ↔
        CategoryTheory.Functor.IsDeformationFunctor F ∧
          (∀ [CategoryTheory.Functor.IsDeformationFunctor F],
            FiniteDimensional k
                (CategoryTheory.Functor.IsPredeformationFunctor.tangentSpace F) ∧
              Function.Injective
                (CategoryTheory.Functor.IsPredeformationFunctor.ofDerivation F)))
