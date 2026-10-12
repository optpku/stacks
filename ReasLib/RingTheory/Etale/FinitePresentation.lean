/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formally Etale Maps of Finite Presentation

This leaf records the map-first finite-presentation criterion relating formal
etaleness and etaleness.

@stack 00UR
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.150.3, tag `00UR`: a finitely presented ring homomorphism is
formally etale if and only if it is etale. -/
@[stacks 00UR "formally etale finite-presentation criterion"]
theorem formallyEtale_iff_etale (f : R →+* S) (hf : f.FinitePresentation) :
    f.FormallyEtale ↔ f.Etale := by
  letI := f.toAlgebra
  change Algebra.FormallyEtale R S ↔ Algebra.Etale R S
  constructor
  · intro h
    exact ⟨h, hf⟩
  · intro h
    exact h.1

end RingHom
