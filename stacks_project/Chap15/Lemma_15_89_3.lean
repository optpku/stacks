/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Torsion.IdealPower
import StacksCheckRecall

/-!
# Lemma 15.89.3

@stack 05EA
-/

@[expose] public section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w} [Finite ι]

/- Lemma 15.89.3 (05EA): for a finite generating family of `I`, the
vanishing of `M[I]`, vanishing of all positive power-torsion stages, and
injectivity of the principal-open localization-family map are equivalent. -/
@[stacks 05EA]
#check fun (I : Ideal R) (f : ι → R) (hI : Ideal.span (Set.range f) = I) ↦
  (LocalizedModule.Away.Cech.powerTorsion_eq_bot_tfae (M := M) I f hI :
    List.TFAE [
      I.powerTorsion M 1 = ⊥,
      ∀ n : ℕ+, I.powerTorsion M (n : ℕ) = ⊥,
      Function.Injective (LocalizedModule.Away.Cech.familyMap M f)
    ])

/- The reusable implication from localization-family injectivity to every
positive power-torsion stage. -/
#check fun (I : Ideal R) (f : ι → R) (hI : Ideal.span (Set.range f) = I)
    (hf : Function.Injective (LocalizedModule.Away.Cech.familyMap M f)) (n : ℕ+) ↦
  (LocalizedModule.Away.Cech.powerTorsion_eq_bot_of_familyMap_injective
      I f hI hf n :
    I.powerTorsion M (n : ℕ) = ⊥)

end
