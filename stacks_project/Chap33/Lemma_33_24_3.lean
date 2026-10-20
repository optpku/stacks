/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Product
import StacksCheckRecall

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.24.3: for quasi-compact morphisms of schemes over a field, the product of their
canonical scheme-theoretic-image factorizations is a scheme-theoretic-image factorization of the
product morphism. -/
@[stacks 04Q1] #check
  (AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticImageFactorization_tensor_overField :
    ∀ {k : Type u} [Field k]
      {A X B Y : Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
      (f : A ⟶ X) (g : B ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f.left] [AlgebraicGeometry.QuasiCompact g.left],
      AlgebraicGeometry.IsSchemeTheoreticImageFactorization ((f ⊗ₘ g).left)
        ((AlgebraicGeometry.Scheme.Hom.toImageOver f ⊗ₘ
          AlgebraicGeometry.Scheme.Hom.toImageOver g).left)
        ((AlgebraicGeometry.Scheme.Hom.imageιOver f ⊗ₘ
          AlgebraicGeometry.Scheme.Hom.imageιOver g).left))
