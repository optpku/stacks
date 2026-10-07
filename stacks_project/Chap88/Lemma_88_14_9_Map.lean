module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap88.Definition_88_14_7_Completion

/-!
# Maps of completed principal localizations

A ring homomorphism `φ : A →+* B` induces
`completedPrincipalLocalization.map φ I f : A_{{f}} →+* B_{{φ f}}` by completing
`Localization.awayMap φ f` along the extended ideals of `I` and `I.map φ`.
-/

@[expose] public section

noncomputable section

universe u v

open AdicCompletion

namespace completedPrincipalLocalization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Powers of the extended ideal of `I` along `Localization.Away f` are contained
in the comap of the corresponding powers of the extended ideal of `I.map φ`
along `Localization.Away (φ f)`, under `Localization.awayMap φ f`. -/
theorem awayMap_pow_le_comap (φ : A →+* B) (I : Ideal A) (f : A) (n : ℕ) :
    (I.map (algebraMap A (Localization.Away f))) ^ n ≤
      (((I.map φ).map (algebraMap B (Localization.Away (φ f)))) ^ n).comap
        (Localization.awayMap φ f) :=
  sorry

/-- The finite-level quotient map of `Localization.awayMap φ f` after evaluating
the source completed principal localization modulo the `n`-th power of the
extended ideal. -/
def mapQuotient (φ : A →+* B) (I : Ideal A) (f : A) (n : ℕ) :
    completedPrincipalLocalization I f →+*
      Localization.Away (φ f) ⧸
        ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) ^ n :=
  (Ideal.quotientMap
      (((I.map φ).map (algebraMap B (Localization.Away (φ f)))) ^ n)
      (Localization.awayMap φ f) (awayMap_pow_le_comap φ I f n)).comp
    (evalₐ (I.map (algebraMap A (Localization.Away f))) n)

/-- The finite-level maps `mapQuotient` are compatible with the inverse-system
transition maps. -/
theorem mapQuotient_compatible (φ : A →+* B) (I : Ideal A) (f : A)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow
        ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) hle).comp
      (mapQuotient φ I f n) =
      mapQuotient φ I f m :=
  sorry

/-- The ring homomorphism `A_{{f}} →+* B_{{φ f}}` obtained by completing
`Localization.awayMap φ f` along the extended ideals of `I` and `I.map φ`. -/
def map (φ : A →+* B) (I : Ideal A) (f : A) :
    completedPrincipalLocalization I f →+* completedPrincipalLocalization (I.map φ) (φ f) :=
  liftRingHom ((I.map φ).map (algebraMap B (Localization.Away (φ f))))
    (mapQuotient φ I f) (fun hle ↦ mapQuotient_compatible φ I f hle)

/-- The completed principal localization square `A → B → B_{{f}}` equals
`A → A_{{f}} → B_{{f}}`. -/
theorem map_comp_of (φ : A →+* B) (I : Ideal A) (f : A) :
    (map φ I f).comp (of I f) = (of (I.map φ) (φ f)).comp φ :=
  sorry

/-- Evaluating `map φ I f` at the `n`-th finite quotient recovers `mapQuotient`. -/
theorem map_eval (φ : A →+* B) (I : Ideal A) (f : A) (n : ℕ) :
    (evalₐ ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) n).toRingHom.comp
        (map φ I f) =
      mapQuotient φ I f n :=
  sorry

end completedPrincipalLocalization

