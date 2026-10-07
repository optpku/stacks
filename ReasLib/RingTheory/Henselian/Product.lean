module

public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products of henselian pairs

Henselianity of a product pair is equivalent to henselianity of every component pair.  The
component-to-product direction is a canonical instance; the reverse direction is an explicit
theorem to avoid a typeclass-search cycle between the product and its components.

@stack 0ATD
-/

@[expose] public section

universe u v

variable {J : Type v} {A : J → Type u} [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))

/-- A henselian product pair gives a henselian pair at every component. -/
theorem HenselianRing.of_pi
    (h : HenselianRing (∀ j, A j) (Ideal.pi I)) (j : J) :
    HenselianRing (A j) (I j) := sorry

/-- A product of henselian pairs is henselian. -/
@[stacks 0ATD "henselian structure on a product pair"]
instance pi_henselianRing [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing (∀ j, A j) (Ideal.pi I) := sorry

/-- Lemma 15.11.11 (0ATD): a product pair is henselian if and only if every component pair is
henselian. -/
@[stacks 0ATD "henselian product pairs"]
theorem henselianRing_pi_iff :
    HenselianRing (∀ j, A j) (Ideal.pi I) ↔ ∀ j, HenselianRing (A j) (I j) := sorry
