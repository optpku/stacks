module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the presentation-to-canonical cotangent comparison

The comparison from the first cotangent homology of an algebra presentation to
the canonical `Algebra.H1Cotangent` is independent of the chosen presentation.
This leaf owns its naturality under morphisms of presentations, without
depending on any chapter-specific construction.
-/

@[expose] public section

open Algebra
open Algebra.Generators
open Algebra.Extension

universe u v w w'

namespace Algebra.Generators

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {ι' : Type w'}
variable {P : Generators R S ι} {P' : Generators R S ι'}

/-- Lemma 10.134.2 [stacks 00S1]: the canonical comparison from the first
cotangent homology of a presentation to `Algebra.H1Cotangent R S` is natural
under morphisms of presentations. -/
@[stacks 00S1 "naturality of the canonical H1 cotangent comparison"]
theorem equivH1Cotangent_naturality (f : P.Hom P') :
    P'.equivH1Cotangent.toLinearMap ∘ₗ Extension.H1Cotangent.map f.toExtensionHom =
      P.equivH1Cotangent.toLinearMap := sorry

end Algebra.Generators
