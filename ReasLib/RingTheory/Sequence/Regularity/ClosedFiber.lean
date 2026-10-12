/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.RingHom
public import ReasLib.RingTheory.Ideal.Quotient.List
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Sequence.Regularity

/-!
# Regular sequences on closed fibers

This leaf owns the reusable list-level conclusions that lift regular sequences from a closed
fiber to a flat local ring.  The Noetherian and essentially-finitely-presented hypotheses are kept
as separate entry points; their one-element input theorems have different mathematical owners.

@stack 00MG
@stack 0470
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.ClosedFiber

open IsLocalRing RingTheory

/-- Lemma 10.99.3, tag `00MG`: a regular sequence on the quotient closed fiber of a flat local
map with Noetherian target lifts to a regular sequence in the target, and all nonempty prefix
quotients stay flat over the base ring. -/
@[stacks 00MG "regular sequences lift from a Noetherian closed fiber"]
theorem isRegular_flat_prefixes
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing S] [Module.Flat R S] (fs : List S)
    (hfs : RingTheory.Sequence.IsRegular
      (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (fs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R))))) :
    RingTheory.Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := sorry

section CanonicalFiber

-- Local instance justification (instance diamond): `Ideal.Fiber` has both tensor actions in scope;
-- the closed-fiber source statement uses Mathlib's canonical right target action.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Lemma 10.128.6, tag `0470`: a regular sequence on the canonical closed fiber of a flat,
essentially finitely presented local map lifts to the target, with flat nonempty prefix quotients. -/
@[stacks 0470 "regular sequences lift from an essentially finitely presented closed fiber"]
theorem isRegular_flat_prefixes_of_essFinitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (fs : List S)
    (hfs : RingTheory.Sequence.IsRegular (Ideal.Fiber (maximalIdeal R) S)
      (fs.map (algebraMap S (Ideal.Fiber (maximalIdeal R) S)))) :
    RingTheory.Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := sorry

end CanonicalFiber

end RingTheory.Sequence.ClosedFiber
