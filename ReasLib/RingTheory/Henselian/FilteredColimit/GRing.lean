/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Regular.GRing

/-!
# Henselian local rings as filtered colimits of G-rings

@stack 0A41

This leaf records a reusable approximation theorem for henselian local rings.
-/

@[expose] public section

open IsLocalRing

universe u

namespace HenselianLocalRing

/-- Lemma 15.50.13 (Tag 0A41): a henselian local ring is a filtered colimit of a directed
system of henselian local G-rings with local transition maps. -/
@[stacks 0A41]
theorem exists_filteredColimit_isGRing
    (A : Type u) [CommRing A] [HenselianLocalRing A] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirectedOrder ι)
      (stage : ι → Type u) (_ : ∀ i : ι, CommRing (stage i))
      (_ : ∀ i : ι, HenselianLocalRing (stage i))
      (_ : ∀ i : ι, IsGRing (stage i))
      (map : ∀ i j : ι, i ≤ j → stage i →+* stage j)
      (_ : DirectedSystem stage (fun i j hij ↦ map i j hij))
      (e : Ring.DirectLimit stage (fun i j hij ↦ map i j hij) ≃+* A),
      ∀ i j (hij : i ≤ j), IsLocalHom (map i j hij) := sorry

end HenselianLocalRing
