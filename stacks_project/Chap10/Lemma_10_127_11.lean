/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_127_11_Tower
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.127.11

@stack 00QV

The directed approximation and its transition-localization property are explicit reusable data in
`DirectedLocalHomApproximation`. The construction of that witness belongs to the proof stage and
does not require chapter-level scalar-tower instances in the statement file.
-/

universe u

section SameUniverse

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- Lemma 10.127.11: an essentially finitely presented local homomorphism of local rings is the
colimit of a directed system of local homomorphisms whose stages are essentially of finite type
and whose transition base changes are localizations at prime ideals. -/
@[stacks 00QV]
theorem exists_localEssFinitePresentationApproximation
    (hf : f.EssFinitePresentation) :
    ∃ A : DirectedLocalHomApproximation.{u, u, u} f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := sorry

end SameUniverse

@[stacks 00QV "directed local finite-presentation approximation"]
#check @exists_localEssFinitePresentationApproximation
