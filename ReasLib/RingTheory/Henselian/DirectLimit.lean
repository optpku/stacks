/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.DirectLimit.Local
public import ReasLib.RingTheory.Henselian.StrictHenselian

@[expose] public section

/-!
# Henselian properties of directed ring colimits

This leaf owns the canonical closure instances for directed colimits of local commutative rings
and of henselian pairs. The carrier is the existing `Ring.DirectLimit`; no presentation-specific
data or chapter-level construction is exposed here.
@stack 04GI
@stack 0FWT
-/

universe u v

namespace Ring.DirectLimit

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type u) [∀ i, CommRing (R i)]
variable (φ : ∀ i j, i ≤ j → R i →+* R j)
variable [DirectedSystem R (φ · · ·)]
variable [∀ i j hij, IsLocalHom (φ i j hij)]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ φ i j h)

/-- Tag 04GI: a directed colimit of henselian local rings along local maps is
henselian.  The directed system and its transition maps are the only data;
the resulting local structure is supplied by the neutral direct-limit API. -/
@[stacks 04GI "henselian directed colimit"]
instance colimitHenselianLocalRing
    [∀ i, HenselianLocalRing (R i)] : HenselianLocalRing R∞ := sorry

/-- Tag 04GI: a directed colimit of strictly henselian local rings along local
maps is strictly henselian.  This extends the canonical henselian colimit
instance and closes the residue field under separable algebraic extensions. -/
@[stacks 04GI "strictly henselian directed colimit"]
instance colimitStrictHenselianLocalRing
    [∀ i, StrictHenselianLocalRing (R i)] : StrictHenselianLocalRing R∞ := sorry

end Ring.DirectLimit

namespace Ring.DirectLimit

variable {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
variable (A : J → Type u) [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))
variable (f : ∀ j k, j ≤ k → A j →+* A k)
variable [DirectedSystem A (f · · ·)]

/-- Lemma 15.11.13 (Stacks `0FWT`): a filtered colimit of henselian pairs is henselian when
the transition maps carry each stage ideal into the next one. -/
@[stacks 0FWT "henselian-pair directed colimit"]
theorem directedSystem_directLimit_henselianRing
    (hI : ∀ ⦃j k⦄ (h : j ≤ k), Ideal.map (f j k h) (I j) ≤ I k)
    [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing (Ring.DirectLimit A (f · · ·))
      (⨆ j, Ideal.map (Ring.DirectLimit.of A (f · · ·) j) (I j)) := sorry

end Ring.DirectLimit
