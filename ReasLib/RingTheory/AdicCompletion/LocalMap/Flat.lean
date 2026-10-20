/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat local maps and maximal-ideal completions

A flat local map of Noetherian local rings which preserves both the maximal ideal and the residue
field induces a bijection on maximal-ideal completions.

@stack 0C4G
@stack 0AGX
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AdicCompletion

/-- Lemma 15.43.8 (Stacks `0C4G`): for a local homomorphism of Noetherian local rings, the
induced map on maximal-ideal completions is flat exactly when the original map is flat. -/
@[stacks 0C4G "flatness and maximal-ideal completion"]
theorem mapLocal_flat_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] :
    (mapLocal f).Flat ↔ f.Flat := sorry

/-- Lemma 15.43.9, Stacks `0AGX`: a flat local map of Noetherian local rings induces a bijection
on maximal-ideal completions when it maps the source maximal ideal onto the target maximal ideal
and induces a bijection on residue fields. -/
@[stacks 0AGX "flat local map induces an isomorphism on completions"]
theorem mapLocal_bijective_of_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hresidue : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Bijective (mapLocal (algebraMap A B)) := sorry

end AdicCompletion
