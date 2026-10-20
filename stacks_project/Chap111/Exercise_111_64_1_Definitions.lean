/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Artinian.Characterizations
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

section
variable {A : Type u} [CommRing A]

/- Exercise 111.64.1 (Definitions): the descending-chain characterization of
Artinian rings, accompanied by the six canonical definitions requested below. -/
@[stacks 0GRT] #check (IsArtinianRing.iff_ideal_antitone_chain_condition :
  IsArtinianRing A ↔ ∀ (chain : ℕ →o (Ideal A)ᵒᵈ),
    ∃ index : ℕ, ∀ later : ℕ, index ≤ later → chain index = chain later)

/- Companion definition (1): a multiplicative subset of a ring `A`. -/
#check (Submonoid A : Type u)

#check (Submonoid.one_mem : ∀ S : Submonoid A, (1 : A) ∈ S)

#check (Submonoid.mul_mem :
  ∀ (S : Submonoid A) {x y : A}, x ∈ S → y ∈ S → x * y ∈ S)

/- Companion definition (2): an Artinian ring `A`. -/
#check (IsArtinianRing A : Prop)

#check (isArtinianRing_iff : IsArtinianRing A ↔ IsArtinian A A)

/- Companion definition (3): the spectrum of a ring `A` as a topological space. -/
#check (PrimeSpectrum A : Type u)

#check PrimeSpectrum.zariskiTopology

#check (inferInstance : TopologicalSpace (PrimeSpectrum A))

end

section
variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/- Companion definition (4): a flat ring map `A →+* B`. -/
#check (φ.Flat : Prop)

#check (RingHom.flat_algebraMap_iff :
  ∀ {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B],
    (algebraMap A B).Flat ↔ Module.Flat A B)

section
variable [Algebra A B]

#check (Module.Flat A B : Prop)

end

end

section
variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

/- Companion definition (5): the height of a prime ideal `p` in `A`. -/
#check (p.height : ℕ∞)

#check (PrimeSpectrum.height_eq_orderHeight :
  ∀ q : PrimeSpectrum A, q.asIdeal.height = Order.height q)

end

section
variable {A : Type u} [CommRing A]

/- Companion definition (6): the functors `Tor (ModuleCat A) i` over a ring `A`. -/
#check (CategoryTheory.Tor (ModuleCat.{u} A) :
  ℕ → ModuleCat.{u} A ⥤ ModuleCat.{u} A ⥤ ModuleCat.{u} A)

#check Tor_obj

#check Tor'

end
