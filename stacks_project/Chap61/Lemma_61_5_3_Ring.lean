/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.WLocalHull.Properties
public import ReasLib.AlgebraicGeometry.WLocalHull.Properties

/-!
# Ring-map properties of w-localization

The structure map `A → A_w` is ind-Zariski and faithfully flat, and the prime
spectrum of `A_w` is a w-local space.
-/

@[expose] public section

universe u

#check (Algebra.WLocalHull.algebraMap_indZariski :
  ∀ (A : Type u) [CommRing A],
    (algebraMap A (Algebra.WLocalHull.wLocalization A)).IndZariski)

#check (Algebra.WLocalHull.instFaithfullyFlat :
  ∀ (A : Type u) [CommRing A],
    Module.FaithfullyFlat A (Algebra.WLocalHull.wLocalization A))

#check (Algebra.WLocalHull.algebraMap_faithfullyFlat :
  ∀ (A : Type u) [CommRing A],
    (algebraMap A (Algebra.WLocalHull.wLocalization A)).FaithfullyFlat)

#check (Algebra.WLocalHull.instWLocalSpace :
  ∀ (A : Type u) [CommRing A],
    WLocalSpace (PrimeSpectrum (Algebra.WLocalHull.wLocalization A)))
