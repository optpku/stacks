/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Uniqueness
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.DerivedCategory

universe u

/- Lemma 86.2.5: let `S` be a scheme. Let `X` be a locally Noetherian algebraic space
over `S`. If `K` and `K'` are dualizing complexes on `X`, then `K'` is isomorphic to
`K ⊗^L L` for some invertible object `L` of `D(𝒪_X)`. -/
@[stacks 0E52] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex.existsInvertibleTensorIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X]
      {K K' : DerivedQCoh X},
      IsDualizingComplex K →
        IsDualizingComplex K' →
          ∃ L : ModuleDerived X,
            (DerivedTensor.Right.functor L).IsEquivalence ∧
              Nonempty (K'.obj ≅ DerivedTensor.Right.obj K.obj L))
