/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.J2.FiniteType
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.19.3 (1): any scheme locally of finite type over a field is J-2. -/
@[stacks 07R5] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isJ2_over_field :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f], Scheme.IsJ2 X)

/- Lemma 29.19.3 (2): any scheme locally of finite type over a Noetherian complete local ring
is J-2. -/
@[stacks 07R5] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isJ2_over_noetherianCompleteLocalRing :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f],
      Scheme.IsJ2 X)

/- Lemma 29.19.3 (3): any scheme locally of finite type over the spectrum of the integers is
J-2. -/
@[stacks 07R5] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isJ2_over_integers :
    ∀ {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f],
      Scheme.IsJ2 X)

/- Lemma 29.19.3 (4): any scheme locally of finite type over a Noetherian local ring of Krull
dimension one is J-2. -/
@[stacks 07R5] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isJ2_over_noetherianLocalRing_of_ringKrullDim_eq_one :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ringKrullDim R = 1 → ∀ {X : Scheme.{u}}
        (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f], Scheme.IsJ2 X)

/- Lemma 29.19.3 (5): any scheme locally of finite type over a Nagata ring of Krull dimension
one is J-2. -/
@[stacks 07R5] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isJ2_over_nagataRing_of_ringKrullDim_eq_one :
    ∀ {R : Type u} [CommRing R] [NagataRing R], ringKrullDim R = 1 →
      ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f],
        Scheme.IsJ2 X)

/- Lemma 29.19.3 (6): any scheme locally of finite type over a Dedekind domain whose fraction
field has characteristic zero is J-2. -/
@[stacks 07R5] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isJ2_over_dedekindDomain_of_fractionRing_charZero :
    ∀ {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f],
      Scheme.IsJ2 X)
