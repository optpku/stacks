/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_159_1.PrefixStageChain
import StacksCheckRecall

@[expose] public section

/-!
Concrete open prefix-stage systems for Lemma 10.159.1.
@stack 03C3
-/

universe u v w

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Lemma 10.159.1 support: a coherent open prefix-stage system below a limit ordinal.
This is the directed-system payload needed before taking the direct limit at the limit stage. -/
@[stacks 03C3 "open prefix-stage system"]
structure OpenPrefixStageSystem
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α) where
  stage :
    (β : Set.Iio α) →
      ResidueExtensionStage.{u, v, max u v} (R := R) K (openPrefixField (R := R) K hα β)
  hom :
    {β γ : Set.Iio α} →
      (hβγ : β ≤ γ) →
        ResidueExtensionStage.Hom.{u, v, max u v, max u v}
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
          (stage β) (stage γ)
  hom_id :
    ∀ β,
      (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (stage β).A
  hom_comp :
    ∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
      ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
          (hom (β := β) (γ := γ) hβγ).toAlgHom) =
        (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom
  base :
    Nonempty
      (ResidueExtensionStage.Hom
        (base_le_prefixField (R := R) (K := K)
          (hα := le_trans (le_of_lt hlimit.bot_lt) hα))
        (ResidueExtensionStage.base (R := R) K)
        (stage ⟨0, hlimit.bot_lt⟩))

end

@[stacks 03C3 "open prefix-stage system"]
#check @OpenPrefixStageSystem
