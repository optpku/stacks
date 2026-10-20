/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.FiniteType

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.17.5 (1): any scheme locally of finite type over a field is universally catenary. -/
@[stacks 02JB] #check
  (AlgebraicGeometry.universallyCatenary_of_locallyOfFiniteType_over_field :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType f], UniversallyCatenary X)

/- Lemma 29.17.5 (2): any scheme locally of finite type over a Cohen-Macaulay scheme is
universally catenary. -/
@[stacks 02JB] #check
  (AlgebraicGeometry.universallyCatenary_of_locallyOfFiniteType_over_cohenMacaulay :
    ∀ {S X : Scheme.{u}} [Scheme.CohenMacaulay S] (f : X ⟶ S)
      [LocallyOfFiniteType f], UniversallyCatenary X)

/- Lemma 29.17.5 (3): any scheme locally of finite type over `Spec(ℤ)` is universally
catenary. -/
@[stacks 02JB] #check
  (AlgebraicGeometry.universallyCatenary_of_locallyOfFiniteType_over_specInt :
    ∀ {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f],
      UniversallyCatenary X)

/- Lemma 29.17.5 (4): any scheme locally of finite type over the spectrum of a one-dimensional
Noetherian domain is universally catenary. -/
@[stacks 02JB] #check
  (AlgebraicGeometry.UniversallyCatenary.of_dimOneDomain :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R],
      ringKrullDim R = 1 → ∀ {X : Scheme.{u}}
        (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f], UniversallyCatenary X)
