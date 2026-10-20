/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- A quasi-finite, finitely presented algebra over a ring with separably
closed residue fields and Hausdorff extremally disconnected prime spectrum has
extremally disconnected prime spectrum. -/
theorem extremallyDisconnected_of_quasiFinite_finitePresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] [Algebra.FinitePresentation A B]
    [T2Space (PrimeSpectrum A)] [ExtremallyDisconnected (PrimeSpectrum A)]
    (h_res : ∀ p : PrimeSpectrum A, IsSepClosed p.asIdeal.ResidueField) :
    ExtremallyDisconnected (PrimeSpectrum B) := sorry

end PrimeSpectrum
