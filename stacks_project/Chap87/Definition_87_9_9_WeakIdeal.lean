/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdeal

/-!
# Weak-ideal index compatibility

The shared formal-spectrum owner supplies the reverse-inclusion index.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.WeakIdealOfDefinition :
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A], Type u)
