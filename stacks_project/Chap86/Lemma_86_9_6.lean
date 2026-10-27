/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 86.9.6: let `S` be a scheme. Consider a cartesian square of algebraic spaces
over `S`. Assume `f : X ⟶ Y` is proper, flat, and of finite presentation. Let
`(ω, τ)` be a relative dualizing complex for `f`. Then `(L(g')^* ω, Lg^* τ)` is a
relative dualizing complex for `f'`. -/
@[stacks 0E6C]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.baseChange :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (_ : RelativeDualizingComplex f),
    @RelativeDualizingComplex S X' Y' f'
      (Proper.of_isPullback sq inferInstance) (Flat.of_isPullback sq inferInstance)
      (FinitePresentation.of_isPullback sq inferInstance))
