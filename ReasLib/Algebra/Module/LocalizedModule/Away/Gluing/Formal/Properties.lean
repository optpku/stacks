module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.OfModule
public import ReasLib.RingTheory.Finiteness.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module properties under formal gluing

Finite generation, finite presentation, flatness, and projectivity can be
tested on the base-change component and the principal-localization components
of a finite formal-gluing cover.

@stack 05EU
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Finite generation is detected by the base change and every
principal-localization component of a finite formal-gluing cover. -/
@[stacks 05EU "finite modules under formal gluing"]
theorem finite_iff_baseChange_and_localizedAway
    [Module.Flat R S]
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
          (algebraMap R S) Ideal.le_comap_map)) :
    Module.Finite R M ↔
      Module.Finite S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.Finite (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) := sorry

/-- Finite presentation is detected by the base change and every
principal-localization component of a finite formal-gluing cover. -/
@[stacks 05EU "finitely presented modules under formal gluing"]
theorem finitePresentation_iff_baseChange_and_localizedAway
    [Module.Flat R S]
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
          (algebraMap R S) Ideal.le_comap_map)) :
    Module.FinitePresentation R M ↔
      Module.FinitePresentation S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.FinitePresentation (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) := sorry

/-- Flatness is detected by the base change and every
principal-localization component of a finite formal-gluing cover. -/
@[stacks 05EU "flat modules under formal gluing"]
theorem flat_iff_baseChange_and_localizedAway
    [Module.Flat R S]
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
          (algebraMap R S) Ideal.le_comap_map)) :
    Module.Flat R M ↔
      Module.Flat S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.Flat (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) := sorry

/-- Projectivity is detected by the base change and every
principal-localization component of a finite formal-gluing cover. -/
@[stacks 05EU "projective modules under formal gluing"]
theorem projective_iff_baseChange_and_localizedAway
    [Module.Flat R S]
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I)
          (algebraMap R S) Ideal.le_comap_map)) :
    Module.Projective R M ↔
      Module.Projective S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.Projective (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) := sorry

end LocalizedModule.Away.FormalGluing
