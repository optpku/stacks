/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPointResidueField
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.50.7: let `S` be a scheme, let `X` and `Y` be integral schemes locally of finite type
over `S`, and let `x ∈ X` and `y ∈ Y` be generic points. Then `X` and `Y` are birational over `S`
if and only if they have isomorphic nonempty open subschemes over `S`, if and only if the
residue-field-valued points at `x` and `y` are isomorphic over `S`. -/
@[stacks 0552] #check
  (AlgebraicGeometry.Scheme.birationalOver_tfae_of_isIntegral_of_locallyOfFiniteType :
    ∀ (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
      [IsIntegral X] [IsIntegral Y]
      [LocallyOfFiniteType (X ↘ S)] [LocallyOfFiniteType (Y ↘ S)]
      (x : X) (y : Y)
      (hx : IsGenericPoint x (Set.univ : Set X))
      (hy : IsGenericPoint y (Set.univ : Set Y)),
        List.TFAE
          [ AlgebraicGeometry.Scheme.BirationalOver (X ↘ S) (Y ↘ S)
          , AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemesOver S X Y
          , AlgebraicGeometry.Scheme.Hom.IsomorphicResidueFieldPointsOver S X Y x y
          ])
