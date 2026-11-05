/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import ReasLib.RingTheory.CompleteIntersection.Local
public import ReasLib.RingTheory.CompleteIntersection.Local.Completion
public import ReasLib.RingTheory.LocalRing.ULift
public import ReasLib.RingTheory.RingHom.TorDimension

/-!
# Complete intersections, completion maps, and residue-field Tor

This leaf owns the local criterion comparing complete-intersection local rings
across a local homomorphism.  Its Tor hypothesis is the map-first specialization
of `CategoryTheory.ModuleCat.Tor.EventuallyIsZero`, and its relative condition
uses the canonical map on maximal-ideal completions and the good-factorization
notion `RingHom.IsCompleteIntersection` of Tag 09QA.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The target of a local ring map has eventually vanishing Tor with the residue field of the
source, expressed in the canonical common-universe representative. -/
abbrev torEventuallyIsZeroAtResidueField (f : A →+* B) [IsLocalRing A] : Prop :=
  ModuleCat.Tor.EventuallyIsZero f.uliftMax.targetModule
    (ModuleCat.of (ULift.{max u v} A) (ResidueField (ULift.{max u v} A)))

namespace HasFiniteTorDimension

/-- Finite Tor dimension implies eventual Tor vanishing against the source
residue field. -/
theorem torEventuallyIsZeroAtResidueField {f : A →+* B} [IsLocalRing A]
    (h : f.HasFiniteTorDimension) :
    f.torEventuallyIsZeroAtResidueField := sorry

end HasFiniteTorDimension

section Local

variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable {f : A →+* B} [IsLocalHom f]

namespace CompleteIntersection

/-- Eventual residue-field Tor vanishing and a complete-intersection target
force the source to be a complete intersection. -/
theorem source_of_target_of_tor
    (hB : IsCompleteIntersectionLocalRing B)
    (hTor : f.torEventuallyIsZeroAtResidueField) :
    IsCompleteIntersectionLocalRing A := sorry

/-- Eventual residue-field Tor vanishing and a complete-intersection target
make the induced completion map a complete-intersection homomorphism in the
good-factorization sense of Tag 09QA. -/
theorem completion_of_target_of_tor
    (hB : IsCompleteIntersectionLocalRing B)
    (hTor : f.torEventuallyIsZeroAtResidueField) :
    (AdicCompletion.mapLocal f).IsCompleteIntersection := sorry

/-- A complete-intersection source and a complete-intersection completion
map force the target to be a complete intersection. -/
theorem target_of_source_of_completion
    (hA : IsCompleteIntersectionLocalRing A)
    (hCompletion : (AdicCompletion.mapLocal f).IsCompleteIntersection) :
    IsCompleteIntersectionLocalRing B := sorry

/-- A complete-intersection source and a complete-intersection completion
map force eventual residue-field Tor vanishing. -/
theorem tor_of_source_of_completion
    (hA : IsCompleteIntersectionLocalRing A)
    (hCompletion : (AdicCompletion.mapLocal f).IsCompleteIntersection) :
    f.torEventuallyIsZeroAtResidueField := sorry

/-- Proposition 23.9.2 (Tag 09QB): for a local homomorphism of Noetherian
local rings, the target complete-intersection condition together with eventual
residue-field Tor vanishing is equivalent to the source complete-intersection
condition together with the good-factorization complete-intersection condition
on the map of maximal-ideal completions. No finite-type hypothesis is imposed. -/
@[stacks 09QB]
theorem target_and_tor_iff_source_and_completion
    (f : A →+* B) [IsLocalHom f] :
    (IsCompleteIntersectionLocalRing B ∧ f.torEventuallyIsZeroAtResidueField) ↔
      (IsCompleteIntersectionLocalRing A ∧
        (AdicCompletion.mapLocal f).IsCompleteIntersection) := by
  constructor
  · rintro ⟨hB, hTor⟩
    exact ⟨source_of_target_of_tor hB hTor, completion_of_target_of_tor hB hTor⟩
  · rintro ⟨hA, hCompletion⟩
    exact ⟨target_of_source_of_completion hA hCompletion,
      tor_of_source_of_completion hA hCompletion⟩

end CompleteIntersection

end Local

end RingHom
