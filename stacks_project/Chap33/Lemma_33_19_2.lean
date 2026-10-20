/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Valuation

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

universe u

/- Lemma 33.19.2 (1): the special fiber is equidimensional. -/
@[stacks 0B2J]
#check
  (AlgebraicGeometry.Scheme.Hom.specialFiber_equidimensional :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of R))
      [IrreducibleSpace X] [LocallyOfFiniteType f] [Surjective f],
      EquidimensionalSpace (Scheme.Hom.fiber f (IsLocalRing.closedPoint R)))

/- Lemma 33.19.2 (2): the special and generic fibers have the same dimension. -/
@[stacks 0B2J]
#check
  (AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_specialFiber_eq_genericFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of R))
      [IrreducibleSpace X] [LocallyOfFiniteType f] [Surjective f],
      topologicalKrullDim (Scheme.Hom.fiber f (IsLocalRing.closedPoint R)) =
        topologicalKrullDim
          (Scheme.Hom.fiber f (genericPoint (Spec (CommRingCat.of R)))))
