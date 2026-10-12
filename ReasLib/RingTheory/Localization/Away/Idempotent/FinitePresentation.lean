/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.TotallySplit
public import ReasLib.RingTheory.Localization.Away.Idempotent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Idempotent localizations from finite presentation

The map-level predicate and its kernel criterion live in the sibling
`Idempotent` leaf.  This leaf adds the algebra-view existence theorem used by
finite-presentation consumers, keeping the flatness and finite-presentation
facts as ambient hypotheses.
-/

universe u v

namespace Algebra.FinitePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.Flat R S] [Algebra.FinitePresentation R S]

/-- Lemma 10.143.9: a surjective flat finitely presented algebra map is localization away from an
idempotent of its source. -/
@[stacks 00U8 "finite-presentation idempotent localization"]
theorem exists_idempotent_localizationAway_of_surjective_of_flat
    (hsurj : Function.Surjective (algebraMap R S)) :
    ∃ e : R, IsIdempotentElem e ∧ IsLocalization.Away e S := by
  let f : R →ₐ[R] S := Algebra.ofId R S
  have hf : Function.Surjective f := hsurj
  have hf_eq : f.toRingHom = algebraMap R S := by
    ext x
    rfl
  let I : Ideal R := RingHom.ker f.toRingHom
  have hfg : I.FG := by
    simpa [I] using Algebra.FinitePresentation.ker_fG_of_surjective f hf
  have hI : IsIdempotentElem I := by
    let e : (R ⧸ I) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective hf
    letI : I.Pure := by
      change Module.Flat R (R ⧸ I)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    exact Ideal.isIdempotentElem_of_pure I
  obtain ⟨e, he, hker⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hI
  refine ⟨1 - e, he.one_sub, ?_⟩
  apply IsLocalization.away_of_isIdempotentElem he.one_sub
  · rw [← hf_eq]
    exact hker.trans (by simp)
  · exact hsurj

end Algebra.FinitePresentation
