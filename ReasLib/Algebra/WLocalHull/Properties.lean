/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Topology.WLocal
public import ReasLib.RingTheory.RingHom.IndZariski
public import ReasLib.Algebra.WLocalHull.WLocalization

/-!
# Ring-map properties of w-localization

The structure map from a commutative ring to its canonical w-localization is
ind-Zariski and faithfully flat, and the prime spectrum of the w-localization is
a w-local space.
-/

@[expose] public section

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- The structure map from a commutative ring to its w-localization is ind-Zariski. -/
theorem algebraMap_indZariski : (algebraMap A (wLocalization A)).IndZariski :=
  sorry

/-- The w-localization of a commutative ring is faithfully flat over that ring. -/
instance instFaithfullyFlat : Module.FaithfullyFlat A (wLocalization A) :=
  sorry

/-- The structure map from a commutative ring to its w-localization is faithfully flat. -/
theorem algebraMap_faithfullyFlat : (algebraMap A (wLocalization A)).FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr (instFaithfullyFlat A)

/-- The prime spectrum of the w-localization of a commutative ring is w-local. -/
instance instWLocalSpace : WLocalSpace (PrimeSpectrum (wLocalization A)) :=
  sorry

end Algebra.WLocalHull
