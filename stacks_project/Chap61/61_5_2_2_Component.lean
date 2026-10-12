/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.Component

/-!
# Component localizations of a vanishing pattern

Given a commutative ring `A` and a finite subset `E`, vanishing patterns index
the complementary decompositions `E = E' ⨿ E''`. Each pattern determines the
locally closed stratum `Z(E', E'') = D(∏ E') ∩ V(span E'')` and the
localization `A_Z^~ = S⁻¹A` of Lemma 61.5.1, where `S` is the preimage of the
units of `(A / I)_f`.
-/

@[expose] public section

universe u

open AlgebraicGeometry.Scheme.WLocalAffine

#check (AlgebraicGeometry.Scheme.WLocalAffine.VanishingPattern :
  {A : Type u} → [CommRing A] → Finset A → Type u)

#check (AlgebraicGeometry.Scheme.WLocalAffine.componentAlgebra :
  {A : Type u} → [CommRing A] → {E : Finset A} → VanishingPattern E → Type u)
