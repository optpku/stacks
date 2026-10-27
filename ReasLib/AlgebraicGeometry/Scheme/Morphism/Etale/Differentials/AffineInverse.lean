/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Kaehler

/-! Affine inverse construction for relative differentials along an etale square. -/

@[expose] public section

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

universe u
open KaehlerDifferential

/-! The affine algebraic input used by the scheme-level comparison.  Mathlib's
`tensorKaehlerEquivOfFormallyEtale` is constructed by a proved `ofBijective`,
so its inverse is genuine data rather than an inverse extracted from an
admitted `IsIso`. -/
noncomputable def affineComparisonInverse (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    [Algebra.FormallyEtale S T] :
    KaehlerDifferential R T ≃ₗ[T] T ⊗[S] KaehlerDifferential R S :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm

/-! Changing the base ring is an equivalence when the base extension is
formally unramified.  The kernel is killed by the exact base-change sequence,
while surjectivity is the native map_surjective theorem. -/
noncomputable def baseRingEquiv
    (R : Type u) (S : Type u) (T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyUnramified R S] :
    KaehlerDifferential R T ≃ₗ[T] KaehlerDifferential S T :=
  LinearEquiv.ofBijective (KaehlerDifferential.map R S T T) ⟨by
    intro x y h
    apply sub_eq_zero.mp
    have hz : KaehlerDifferential.map R S T T (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨q, hq⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S T (x - y)).mp hz
    have hq0 : q = 0 := Subsingleton.elim _ _
    rw [hq0, map_zero] at hq
    exact hq.symm,
    KaehlerDifferential.map_surjective R S T⟩

noncomputable def squareEquiv
    (A : Type u) (A' : Type u) (B : Type u) (B' : Type u)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B']
    [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [Algebra.FormallyEtale B B'] [Algebra.FormallyUnramified A A'] :
    B' ⊗[B] KaehlerDifferential A B ≃ₗ[B'] KaehlerDifferential A' B' :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B B').trans
    (baseRingEquiv A A' B')

end AlgebraicGeometry.Scheme.RelativeDifferentials
