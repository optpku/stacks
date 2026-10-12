/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.RingTheory.Algebra.IsEpi.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-injective complexes under change of rings

@stack 0915
@stack 0916
@stack 0917

This file records the three standard change-of-rings operations on K-injective cochain complexes:
flat restriction, arbitrary coextension, and reflection along a ring epimorphism.
-/

@[expose] public section

open CategoryTheory ComplexShape

universe u

namespace ModuleCat.RestrictScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.56.1 (0915): restriction of scalars along a flat commutative ring map preserves
K-injective cochain complexes. -/
@[stacks 0915]
theorem isKInjective_of_flat
    (f : R →+* S) (h_flat : f.Flat)
    (I : CochainComplex (ModuleCat.{u} S) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj I) := sorry

end ModuleCat.RestrictScalars

namespace ModuleCat.CoextendScalars

variable {R S : Type u} [Ring R] [Ring S]

/-- Lemma 15.56.3 (0917): coextension of scalars sends K-injective cochain complexes to
K-injective cochain complexes. -/
@[stacks 0917]
theorem isKInjective
    (f : R →+* S) (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((ModuleCat.coextendScalars f).mapHomologicalComplex (up ℤ)).obj I) := sorry

end ModuleCat.CoextendScalars

namespace ModuleCat.RestrictScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.56.2 (0916): restriction of scalars along a ring epimorphism reflects
K-injectivity. -/
@[stacks 0916]
theorem isKInjective_of_epi
    (f : R →+* S) [Epi (CommRingCat.ofHom f)]
    (I : CochainComplex (ModuleCat.{u} S) ℤ)
    [CochainComplex.IsKInjective
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (up ℤ)).obj I)] :
    I.IsKInjective := sorry

end ModuleCat.RestrictScalars
