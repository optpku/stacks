/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericFiber
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.51.4: for a locally finite type morphism `f : X ⟶ Y` and a generic point `η`
of an irreducible component of `Y`, the point-set fiber over `η` consists entirely of generic
points of `X` if and only if `f` is quasi-finite at every point over `η`, equivalently at every
generic point of `X` over `η`. -/
@[stacks 0BAH] #check
  (AlgebraicGeometry.Scheme.Hom.tfae_fiber_subset_genericPoints_quasiFiniteAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {η : Y},
      η ∈ genericPoints Y →
        List.TFAE
          [ (∀ x : X, f x = η → x ∈ genericPoints X)
          , (∀ x : X, f x = η → f.QuasiFiniteAt x)
          , (∀ x : X, x ∈ genericPoints X → f x = η → f.QuasiFiniteAt x)
          ])
