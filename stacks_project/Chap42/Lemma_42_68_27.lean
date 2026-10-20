/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Quotient

@[expose] public section

universe u v

/- Lemma 42.68.27 (1): if `φ` and `ψ` are injective endomorphisms of a finite
dimension-one module over a Noetherian local ring and their composite ranges agree, then the
quotient by `range (φ.comp ψ)` has finite length. -/
@[stacks 02PX]
#check (CategoryTheory.TwoPeriodicEndomorphism.quotientComp_length_lt_top :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (φ ψ : Module.End A M), Function.Injective φ → Function.Injective ψ →
      (φ.comp ψ).range = (ψ.comp φ).range → Module.supportDim A M = 1 →
        Module.length A (M ⧸ (φ.comp ψ).range) < ⊤)

/- Lemma 42.68.27 (2): under the same hypotheses, the quotient equipped with the maps induced
by `φ` and `ψ` is an acyclic two-periodic endomorphism complex. When `φ` and `ψ` commute,
the equality of composite ranges follows by applying `LinearMap.range` to that equality. -/
@[stacks 02PX]
#check (CategoryTheory.TwoPeriodicEndomorphism.quotientComp_acyclic :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (φ ψ : Module.End A M), Function.Injective φ → Function.Injective ψ →
      (hRange : (φ.comp ψ).range = (ψ.comp φ).range) → Module.supportDim A M = 1 →
        (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp φ ψ hRange).toCochainComplex.Acyclic)
