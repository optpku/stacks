/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.RingTheory.Smooth.AtPrime
import StacksCheckRecall

/-!
@stack 07BU
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for the local smoothness criterion:
- primary domain: commutative algebra of smooth ring maps, localized cotangent homology, and
  localized Kähler differentials at a prime;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.SmoothAtPrime.iff_isSmoothAt`,
  `Algebra.smoothLocus_eq_compl_support_inter`,
  `Module.free_of_flat_of_isLocalRing`,
  `module_finite_projective_iff_finitePresentation_and_flat`;
- best owner abstraction: the source-facing owner at this stage is `Algebra.SmoothAtPrime`,
  with `Algebra.IsSmoothAt` used only as the canonical local bridge;
- primitive data: the prime `q`, the local ring `S_q`, the localized cotangent homology, and the
  localized module of Kähler differentials;
- derived API: the finite-free/projective/flat reformulations of the same localized criterion.

Source/core/bridge triage:
- `source-facing`: the textbook `List.TFAE` statement with first clause `SmoothAtPrime R S q`;
- `core/canonical`: `Algebra.IsSmoothAt`, the localized cotangent-homology support criterion, and
  the local-ring projective/free criterion;
- `bridge/view`: `SmoothAtPrime.iff_isSmoothAt`, used internally to pass from the source-facing
  predicate to the canonical local owner.

This file remains `source-facing`: it keeps the textbook `List.TFAE` packaging while exposing the
canonical local criterion only through a private bridge theorem.
-/

variable [FinitePresentation R S]

section

variable (q : PrimeSpectrum S)

local notation "S₍q₎" => Localization.AtPrime q.asIdeal
local notation "H¹₍q₎" => LocalizedModule.AtPrime q.asIdeal (H1Cotangent R S)
local notation "Ω₍q₎" => LocalizedModule.AtPrime q.asIdeal Ω[S⁄R]

private theorem isSmoothAt_iff_subsingleton_localizedH1Cotangent_and_localizedKaehler_free
    :
    IsSmoothAt R q.asIdeal ↔
      Subsingleton H¹₍q₎ ∧
        Module.Free S₍q₎ Ω₍q₎ := by
  change q ∈ smoothLocus R S ↔ _
  rw [smoothLocus_eq_compl_support_inter]
  simp only [Set.mem_inter_iff, Set.mem_compl_iff,
    Module.notMem_support_iff, Module.mem_freeLocus]

-- Proof sketch: use `Algebra.smoothLocus_eq_compl_support_inter` to identify `IsSmoothAt R q.asIdeal`
-- with vanishing of the localized cotangent homology and freeness of the localized Kähler
-- differentials. Since `R → S` is finitely presented, `Ω[S⁄R]` is finitely presented over `S`, so
-- after localizing at `q` the local module criterion for finite projective modules identifies the
-- finite-free, projective, and flat clauses over the local ring `S_q`.
namespace SmoothAtPrime

/-- Lemma 10.137.11: for a finitely presented ring map `R → S` and a prime `q` of `S`, the
following are equivalent: `R → S` is smooth at `q` in the source-facing sense `SmoothAtPrime R S q`;
the localized first cotangent homology `H¹(L_{S/R})_q` vanishes and the localized module of Kähler
differentials `Ω[S⁄R]_q` is finite free over `S_q`; `H¹(L_{S/R})_q` vanishes and `Ω[S⁄R]_q` is
projective over `S_q`; and `H¹(L_{S/R})_q` vanishes and `Ω[S⁄R]_q` is flat over `S_q`. -/
@[stacks 07BU]
theorem tfae
    :
    List.TFAE
      [ SmoothAtPrime R S q
      , Subsingleton H¹₍q₎ ∧
          Module.Finite S₍q₎ Ω₍q₎ ∧
          Module.Free S₍q₎ Ω₍q₎
      , Subsingleton H¹₍q₎ ∧
          Module.Projective S₍q₎ Ω₍q₎
      , Subsingleton H¹₍q₎ ∧
          Module.Flat S₍q₎ Ω₍q₎
      ] := by
  have hsmooth :
      SmoothAtPrime R S q ↔
        Subsingleton H¹₍q₎ ∧ Module.Free S₍q₎ Ω₍q₎ :=
    (SmoothAtPrime.iff_isSmoothAt R S q).trans
      (isSmoothAt_iff_subsingleton_localizedH1Cotangent_and_localizedKaehler_free q)
  have hfree_projective :
      Module.Free S₍q₎ Ω₍q₎ ↔ Module.Projective S₍q₎ Ω₍q₎ := by
    constructor
    · intro hfree
      letI := hfree
      infer_instance
    · intro hprojective
      letI := hprojective
      exact Module.free_of_flat_of_isLocalRing
  have hfree_flat : Module.Free S₍q₎ Ω₍q₎ ↔ Module.Flat S₍q₎ Ω₍q₎ := by
    constructor
    · intro hfree
      letI := hfree
      infer_instance
    · intro hflat
      letI := hflat
      exact Module.free_of_flat_of_isLocalRing
  apply List.tfae_of_forall (SmoothAtPrime R S q)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rfl
  · have hfinite : Module.Finite S₍q₎ Ω₍q₎ := inferInstance
    exact (and_congr Iff.rfl (and_iff_right hfinite)).trans hsmooth.symm
  · exact (and_congr Iff.rfl hfree_projective.symm).trans hsmooth.symm
  · exact (and_congr Iff.rfl hfree_flat.symm).trans hsmooth.symm

end SmoothAtPrime

end

end Algebra

#check @Algebra.SmoothAtPrime.iff_isSmoothAt
#check @Algebra.smoothLocus_eq_compl_support_inter
#check @Module.free_of_flat_of_isLocalRing
#check @Algebra.SmoothAtPrime.tfae

#print axioms Algebra.SmoothAtPrime.tfae
