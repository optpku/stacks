/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.LocallyFree.Rank

/-!
# Criteria for finite locally free modules

@stack 00NX
-/

@[expose] public section

universe u v

namespace Module.FiniteLocallyFree

/-- Lemma 10.78.2 (Stacks `00NX`): the standard finite-presentation,
projectivity, local-freeness, and rank criteria for a finite locally free
module. -/
@[stacks 00NX]
theorem tfae {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] :
    List.TFAE
      [ Module.FinitePresentation R M ∧ Module.Flat R M
      , Module.Finite R M ∧ Module.Projective R M
      , ∃ (ι : Type (max u v)) (_ : Finite ι)
          (i : M →ₗ[R] (ι → R)) (s : (ι → R) →ₗ[R] M),
          s.comp i = LinearMap.id
      , Module.FinitePresentation R M ∧ Module.freeLocus R M = Set.univ
      , Module.FinitePresentation R M ∧
          ∀ (P : Ideal R) [P.IsMaximal],
            Module.Free (Localization.AtPrime P) (LocalizedModule.AtPrime P M)
      , Module.Finite R M ∧ Module.LocallyFree R M
      , Module.FiniteLocallyFree R M
      , Module.Finite R M ∧
          Module.freeLocus R M = Set.univ ∧
            IsLocallyConstant
              (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk M p : ℤ))
      ] := sorry

end Module.FiniteLocallyFree
