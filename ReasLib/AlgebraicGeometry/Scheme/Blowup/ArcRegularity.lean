/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.PointSequence
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import ReasLib.RingTheory.Completion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Hom

-- Local instance justification (search instability): `Localization.AtPrime (RingHom.ker f)` needs the canonical primality theorem, which mathlib does not register globally.
attribute [local instance] RingHom.ker_isPrime

/-- A complete-DVR arc from a two-dimensional Noetherian local domain reaches the regular locus
after finitely many compatible point blowups when the kernel localization is regular. -/
theorem exists_mem_regularLocus_of_regular_ker
    (A R : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (f : A →+* R) (hf : Function.Surjective f) (hdim : ringKrullDim A = 2)
    (S : PointBlowupSequence (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint R))
    (hker : IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))) :
    ∃ i : ℕ, S.point i ∈ regularLocus (S.stage i) := sorry

end AlgebraicGeometry.Scheme
