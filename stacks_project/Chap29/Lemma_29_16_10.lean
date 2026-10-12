/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/-
Lemma 29.16.10 (1): any scheme locally of finite type over a field is Jacobson.
-/
@[stacks 02J6] #check
  (AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace_over_field :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType f],
      JacobsonSpace X)

/-
Lemma 29.16.10 (2): any scheme locally of finite type over `Spec(ℤ)` is Jacobson.
-/
@[stacks 02J6] #check
  (AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace_over_integers :
    ∀ {X : AlgebraicGeometry.Scheme}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of ℤ))
      [AlgebraicGeometry.LocallyOfFiniteType f],
      JacobsonSpace X)

/-
Lemma 29.16.10 (3): any scheme locally of finite type over `Spec(R)` is Jacobson when `R` is a
one-dimensional Noetherian domain with infinitely many prime ideals.
-/
@[stacks 02J6] #check
  (AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace_over_spec_of_ringKrullDim_eq_one :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [Infinite (PrimeSpectrum R)], ringKrullDim R = 1 →
      ∀ {X : AlgebraicGeometry.Scheme.{u}}
        (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
        [AlgebraicGeometry.LocallyOfFiniteType f],
        JacobsonSpace X)

/-
Lemma 29.16.10 (4): the punctured spectrum of a Noetherian local ring is Jacobson.
-/
@[stacks 02J6] #check
  (AlgebraicGeometry.jacobsonSpace_puncturedSpectrum_of_isNoetherianRing :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      JacobsonSpace (AlgebraicGeometry.PuncturedSpectrum.scheme A))

/-
Lemma 29.16.10 (5): any scheme locally of finite type over the punctured spectrum of a
Noetherian local ring is Jacobson.
-/
@[stacks 02J6] #check
  (AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace_over_puncturedSpectrum :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.PuncturedSpectrum.scheme A)
      [AlgebraicGeometry.LocallyOfFiniteType f],
      JacobsonSpace X)
