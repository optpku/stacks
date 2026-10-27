/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent.Permanence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma (0HAD) (1): Any scheme locally of finite type over a field is excellent. -/
@[stacks 0HAD] #check
  (AlgebraicGeometry.Scheme.excellent_of_locallyOfFiniteType_field : ∀ {X : Scheme.{u}}
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f], Scheme.Excellent X)

/- Lemma (0HAD) (2): Any scheme locally of finite type over a Noetherian complete
local ring is excellent. Completeness is taken with respect to the maximal ideal. -/
@[stacks 0HAD] #check
  (AlgebraicGeometry.Scheme.excellent_of_locallyOfFiniteType_completeLocal : ∀ {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f], Scheme.Excellent X)

/- Lemma (0HAD) (3): Any scheme locally of finite type over ℤ is excellent.
The base is presented as ULift.{u} ℤ to match the scheme universe. -/
@[stacks 0HAD] #check
  (AlgebraicGeometry.Scheme.excellent_of_locallyOfFiniteType_int : ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) [LocallyOfFiniteType f],
    Scheme.Excellent X)

/- Lemma (0HAD) (4): Any scheme locally of finite type over a characteristic-zero
Dedekind domain is excellent. -/
@[stacks 0HAD] #check
  (AlgebraicGeometry.Scheme.excellent_of_locallyOfFiniteType_dedekindCharZero : ∀ {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f], Scheme.Excellent X)
