/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OverField.Birational

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.4.2: for varieties `X` and `Y` over a field `k`, birationality over `k`,
isomorphism of their function fields as `k`-algebras, existence of isomorphic nonempty open
subschemes over `k`, and existence of a birational `k`-morphism from an open subscheme of `X` to
`Y` are equivalent. -/
@[stacks 0BXP] #check
  (AlgebraicGeometry.SchemeOverField.birational_tfae :
    ∀ {k : Type u} [Field k]
      (X Y : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Variety X] [AlgebraicGeometry.Variety Y],
      List.TFAE
        [ AlgebraicGeometry.Scheme.BirationalOver X.hom Y.hom
        , Nonempty
            (AlgebraicGeometry.SchemeOverField.functionFieldCommAlg X ≅
              AlgebraicGeometry.SchemeOverField.functionFieldCommAlg Y)
        , AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemesOver
            (AlgebraicGeometry.Spec (CommRingCat.of k)) X.left Y.left
        , AlgebraicGeometry.SchemeOverField.HasBirationalOpenTo X Y
        ])
