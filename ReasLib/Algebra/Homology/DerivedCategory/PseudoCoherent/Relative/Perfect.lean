/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative perfect objects

An `R`-perfect object of the derived category of `A`-modules is pseudo-coherent over `A` and has
finite Tor dimension after restriction of scalars to `R`.  The predicate is defined for every
commutative `R`-algebra; flatness and finite presentation are hypotheses of the geometric results
that use it, not part of the intrinsic predicate.

@stack 0DHS
@stack 0DHT
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u

namespace CategoryTheory.DerivedCategory

/-- Definition 15.84.1 (Stacks `0DHS`): the object property on `D(A)` of being perfect relative
to the base commutative ring `R`.  Its members are pseudo-coherent over `A` and have finite Tor
dimension over `R` after restriction of scalars. -/
@[stacks 0DHS]
def perfectOver
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    ObjectProperty (DerivedCategory (ModuleCat A)) :=
  fun K ↦ K.IsPseudoCoherent ∧
    HasFiniteTorDimensionOver R K

/-- Object-level spelling of membership in the relative-perfect object property. -/
@[stacks 0DHS "relative-perfect derived objects"]
abbrev IsPerfectOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) : Prop :=
  perfectOver R A K

/-- A relative-perfect object is equivalently a pseudo-coherent `A`-complex whose restricted
`R`-complex has finite Tor dimension. -/
@[stacks 0DHS "relative-perfectness characterization"]
theorem isPerfectOver_iff
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) :
    IsPerfectOver R K ↔
      K.IsPseudoCoherent ∧
        HasFiniteTorDimensionOver R K := sorry
/- Proof strategy: unfold `IsPerfectOver` and `perfectOver`; membership in the defining
intersection is exactly the displayed conjunction. -/

/-- The pseudo-coherent component of relative perfectness. -/
@[stacks 0DHS "pseudo-coherent component"]
theorem IsPerfectOver.isPseudoCoherent
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {K : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K) :
    K.IsPseudoCoherent := sorry
/- Proof strategy: rewrite `hK` with `isPerfectOver_iff` and take its pseudo-coherent
component. -/

/-- The finite-Tor component of relative perfectness. -/
@[stacks 0DHS "finite-Tor component"]
theorem IsPerfectOver.hasFiniteTorDimensionOver
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {K : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K) :
    K.HasFiniteTorDimensionOver R := sorry
/- Proof strategy: rewrite `hK` with `isPerfectOver_iff` and take its finite-Tor-dimension
component. -/

/-- Lemma 15.84.2 (Stacks `0DHT`), saturation clause: relative-perfect objects are stable under
retracts. -/
@[stacks 0DHT "saturated"]
instance perfectOver_isStableUnderRetracts
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    (perfectOver R A).IsStableUnderRetracts := sorry
/- Proof strategy: use `isPerfectOver_iff` and combine retract stability of
`DerivedCategory.IsPseudoCoherent` with retract stability of
`HasFiniteTorDimensionOver R`; restriction of scalars preserves the retract diagram. -/

/-- Lemma 15.84.2 (Stacks `0DHT`), strict-fullness clause: relative perfectness transports
across an isomorphism in `D(A)`. -/
@[stacks 0DHT "strictly full"]
theorem IsPerfectOver.ofIso
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {K L : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K) (e : K ≅ L) :
    IsPerfectOver R L := sorry
/- Proof strategy: split with `isPerfectOver_iff`, transport pseudo-coherence and finite Tor
dimension along `e`, and reassemble the two components. -/

/-- Lemma 15.84.2 (Stacks `0DHT`), triangulated clause: relative-perfect objects form a
triangulated object property. -/
@[stacks 0DHT "triangulated"]
instance perfectOver_isTriangulated
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    (perfectOver R A).IsTriangulated := sorry
/- Proof strategy: express `perfectOver` as the intersection of pseudo-coherence and finite Tor
dimension after exact restriction of scalars, then combine the existing triangulated-object-property
instances for those two predicates. -/

end CategoryTheory.DerivedCategory

end
