/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.ClosedMapCriteria
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 32.14.3: for a separated finite-type morphism of schemes, properness is equivalent to
closedness after every locally finite-type base change and to closedness after every
finite-dimensional relative affine-space base change. -/
@[stacks 0205] #check
  (AlgebraicGeometry.IsProper.tfae_isClosedMap_baseChange :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [Scheme.Hom.FiniteType f],
      List.TFAE
        [ IsProper f
        , ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFiniteType g →
            IsClosedMap (pullback.snd f g).base
        , ∀ n : ℕ,
            IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base
        ])
