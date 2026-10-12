/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Generated.Properties
public import ReasLib.RingTheory.RegularLocalRing.Parameters
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic Formal Smoothness and Regular Local Rings

For a Noetherian local algebra over a field, maximal-ideal-adic formal smoothness implies
regularity.  Separability of the residue-field extension gives the converse.

@stack 07EI
@stack 07EJ
-/

@[expose] public section

open IsLocalRing

universe u v

/-- Lemma 15.38.2 (Stacks `07EI`): a Noetherian local algebra over a field is regular when its
structure map is formally smooth for the maximal-ideal-adic topology. -/
@[stacks 07EI "adic formal smoothness implies regularity"]
theorem isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hfs : (algebraMap k A).formally_smooth_for_adic (maximalIdeal A)) :
    IsRegularLocalRing A := sorry

/-- Lemma 15.38.5 (Stacks `07EJ`): a regular local algebra over a field is formally smooth for
its maximal-ideal-adic topology when its residue-field extension is separable. -/
@[stacks 07EJ "regularity and residue separability imply adic formal smoothness"]
theorem formallySmooth_for_maximalIdeal_adic_of_isRegularLocalRing_of_isSeparableOver
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [IsRegularLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := sorry
