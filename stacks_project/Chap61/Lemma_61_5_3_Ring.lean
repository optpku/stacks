/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import stacks_project.Chap61.Definition_61_2_3_WLocal
public import stacks_project.Chap61.Definition_61_4_1_IndZariski
public import stacks_project.Chap61.«61_5_2_5_WLocalization»

/-!
# Ring-map properties of w-localization

The structure map `A → A_w` is ind-Zariski and faithfully flat, and the prime
spectrum of `A_w` is a w-local space.
-/

@[expose] public section

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- The structure map `A → A_w` is ind-Zariski. -/
theorem algebraMap_indZariski : (algebraMap A (wLocalization A)).IndZariski :=
  sorry

/-- The w-localization `A_w` is faithfully flat as an `A`-algebra. -/
instance instFaithfullyFlat : Module.FaithfullyFlat A (wLocalization A) :=
  sorry

/-- The structure map `A → A_w` is faithfully flat. -/
theorem algebraMap_faithfullyFlat : (algebraMap A (wLocalization A)).FaithfullyFlat :=
  sorry

/-- The prime spectrum of the w-localization `A_w` is a w-local space. -/
instance instWLocalSpace : WLocalSpace (PrimeSpectrum (wLocalization A)) :=
  sorry

end Algebra.WLocalHull
