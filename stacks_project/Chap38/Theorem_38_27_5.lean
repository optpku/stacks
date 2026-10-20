/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions.Representation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Theorem 38.27.5: in Situation 38.20.11, if `f` and `ℱ` are finitely presented and
`ℱ` is pure relative to `S`, then `F_n` is represented by a finitely presented monomorphism
`Z_n ⟶ S`. -/
@[stacks 05UG] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor.existsMonomorphismRepresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] (n : ℕ), ℱ.IsPureOver f →
        ∃ Z : Over S,
          Nonempty
            ((AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor
              f ℱ n).RepresentableBy Z) ∧
            Mono Z.hom ∧ AlgebraicGeometry.Scheme.Hom.FinitePresentation Z.hom)
