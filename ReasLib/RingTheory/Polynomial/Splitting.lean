/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FiniteFree
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Syntomic Splitting Extensions of Monic Polynomials

This leaf strengthens the finite-free splitting extension supplied by Mathlib
with the syntomic and faithfully-flat properties needed in relative algebraic
geometry.

@stack 03HS
-/

universe u

namespace Polynomial.Monic

variable {R : Type u} [CommRing R]

/-- Lemma 10.136.14, tag `03HS`: a monic polynomial splits after a syntomic,
finite-free, faithfully flat extension of its coefficient ring. -/
@[stacks 03HS "syntomic faithfully flat splitting extension of a monic polynomial"]
theorem exists_syntomic_faithfullyFlat_splits_map {p : R[X]} (hp : p.Monic) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S)
      (_ : (algebraMap R S).FiniteFree) (_ : (algebraMap R S).Syntomic)
      (_ : (algebraMap R S).FaithfullyFlat),
        (p.map (algebraMap R S)).Splits := sorry

end Polynomial.Monic
