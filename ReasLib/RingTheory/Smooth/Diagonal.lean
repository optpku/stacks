/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication.Perfect
public import ReasLib.RingTheory.EssentialFiniteness
public import ReasLib.RingTheory.Smooth.EssSmooth

/-!
# Smoothness from finite Tor dimension of the diagonal

Theorems in this leaf recognize smooth and essentially smooth algebras from
flatness and finite Tor dimension of tensor-square multiplication.

@stack 0FCW
@stack 0FCX
-/

@[expose] public section

universe u v

namespace RingHom

namespace DiagonalIsPerfect

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsNoetherianRing B]

/-- For an essentially finite-type map to a Noetherian target, perfectness of tensor-square
multiplication is equivalent to finite Tor dimension: pseudo-coherence is automatic. -/
theorem iff_hasFiniteTorDimension (f : A →+* B) (hfinite : f.EssFiniteType) :
    f.DiagonalIsPerfect ↔ f.DiagonalHasFiniteTorDimension := sorry

end DiagonalIsPerfect

section EssentiallySmooth

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Lemma 23.10.1 (0FCW): a flat, essentially finite-type local map of Noetherian local rings is
essentially smooth when its diagonal is perfect. -/
@[stacks 0FCW "map-first perfect-diagonal criterion"]
theorem EssSmooth.of_diagonal_isPerfect (f : A →+* B) [IsLocalHom f]
    (hfinite : f.EssFiniteType) (hflat : f.Flat) (hdiag : f.DiagonalIsPerfect) :
    f.EssSmooth := sorry

/-- Lemma 23.10.1 (0FCW), in the source's finite-Tor form: a flat, essentially finite-type local
map of Noetherian local rings is essentially smooth when its diagonal has finite Tor dimension. -/
@[stacks 0FCW "map-first finite-Tor diagonal criterion"]
theorem EssSmooth.of_diagonal_hasFiniteTorDimension (f : A →+* B) [IsLocalHom f]
    (hfinite : f.EssFiniteType) (hflat : f.Flat)
    (hdiag : f.DiagonalHasFiniteTorDimension) :
    f.EssSmooth := sorry

end EssentiallySmooth

section Smooth

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/-- Lemma 23.10.2 (0FCX): a flat finite-type map of Noetherian rings is smooth when its diagonal
is perfect. -/
@[stacks 0FCX "map-first perfect-diagonal criterion"]
theorem Smooth.of_diagonal_isPerfect (f : A →+* B)
    (hfinite : f.FiniteType) (hflat : f.Flat) (hdiag : f.DiagonalIsPerfect) :
    f.Smooth := sorry

/-- Lemma 23.10.2 (0FCX), in the source's finite-Tor form: a flat finite-type map of Noetherian
rings is smooth when its diagonal has finite Tor dimension. -/
@[stacks 0FCX "map-first finite-Tor diagonal criterion"]
theorem Smooth.of_diagonal_hasFiniteTorDimension (f : A →+* B)
    (hfinite : f.FiniteType) (hflat : f.Flat)
    (hdiag : f.DiagonalHasFiniteTorDimension) :
    f.Smooth := sorry

end Smooth

end RingHom

namespace Algebra

section EssentiallySmooth

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra.EssFiniteType A B] [Module.Flat A B]

/-- Lemma 23.10.1 (0FCW), algebra form: a flat essentially finite-type local map of Noetherian
local rings is essentially smooth when tensor-square multiplication is a perfect ring map. -/
@[stacks 0FCW]
theorem EssSmooth.of_diagonal_isPerfect
    (hdiag : (tensorSquareMultiplication A B).IsPerfectRingMap) :
    EssSmooth A B := sorry

/-- Lemma 23.10.1 (0FCW), algebra form with the source's finite-Tor hypothesis. -/
@[stacks 0FCW "algebra finite-Tor diagonal criterion"]
theorem EssSmooth.of_diagonal_hasFiniteTorDimension
    (hdiag : (tensorSquareMultiplication A B).HasFiniteTorDimension) :
    EssSmooth A B := sorry

end EssentiallySmooth

section Smooth

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra.FiniteType A B] [Module.Flat A B]

/-- Lemma 23.10.2 (0FCX), algebra form: a flat finite-type map of Noetherian rings is smooth when
tensor-square multiplication is a perfect ring map. -/
@[stacks 0FCX]
theorem Smooth.of_diagonal_isPerfect
    (hdiag : (tensorSquareMultiplication A B).IsPerfectRingMap) :
    Smooth A B := sorry

/-- Lemma 23.10.2 (0FCX), algebra form with the source's finite-Tor hypothesis. -/
@[stacks 0FCX "algebra finite-Tor diagonal criterion"]
theorem Smooth.of_diagonal_hasFiniteTorDimension
    (hdiag : (tensorSquareMultiplication A B).HasFiniteTorDimension) :
    Smooth A B := sorry

end Smooth

end Algebra
