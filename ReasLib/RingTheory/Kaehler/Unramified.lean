/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kähler differentials under unramified source change

This leaf records the atomic source-change consequences of the Kähler
transitivity sequence when the source extension has trivial differentials.

@stack 00S2
@stack 00RT
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace KaehlerDifferential

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Tag `00S2`: if the source Kähler differentials are subsingleton, then the
terminal Kähler map in the transitivity sequence is injective.  The vanishing
hypothesis is explicit so callers can supply a one-off argument without a
temporary instance. -/
@[stacks 00S2 "Kahler source-change injectivity"]
theorem map_injective_of_subsingleton
    (hΩ : Subsingleton Ω[S⁄R]) :
    Function.Injective (map R S T T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R S T x).mp hx
  clear hx
  induction y with
  | zero => exact map_zero _
  | tmul t s =>
      rw [mapBaseChange_tmul, hΩ.elim s 0, map_zero, smul_zero]
  | add y z hy hz => rw [map_add, hy, hz, zero_add]

/-- Tag `00S2`: if the source Kähler differentials are subsingleton, then the
terminal Kähler map in the transitivity sequence is bijective. -/
@[stacks 00S2 "Kahler source-change bijectivity"]
theorem map_bijective_of_subsingleton
    (hΩ : Subsingleton Ω[S⁄R]) :
    Function.Bijective (map R S T T) := by
  exact ⟨map_injective_of_subsingleton hΩ, map_surjective R S T⟩

/-- Tag `00S2`: a formally unramified source map makes the terminal Kähler
map in the transitivity sequence bijective. -/
@[stacks 00S2 "Kahler source-change bijectivity for formally unramified maps"]
theorem map_bijective_of_formallyUnramified
    [Algebra.FormallyUnramified R S] :
    Function.Bijective (map R S T T) := by
  exact map_bijective_of_subsingleton
    (inferInstance : Subsingleton Ω[S⁄R])

/-- Tag `00S2`: a formally etale source map makes the terminal Kähler map in
the transitivity sequence bijective. -/
@[stacks 00S2 "Kahler source-change bijectivity for formally etale maps"]
theorem map_bijective_of_formallyEtale
    [Algebra.FormallyEtale R S] :
    Function.Bijective (map R S T T) := by
  exact map_bijective_of_subsingleton
    (inferInstance : Subsingleton Ω[S⁄R])

/-- Lemma 10.131.8 (1), tag `00RT`: localizing the source algebra induces a
bijective canonical map on Kähler differentials. -/
@[stacks 00RT]
theorem map_bijective_of_isLocalization_source
    (M : Submonoid R) [IsLocalization M S] :
    Function.Bijective (map R S T T) := sorry

end KaehlerDifferential
