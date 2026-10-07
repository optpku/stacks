module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Locality
import StacksCheckRecall

/-!
# Lemma 15.81.8 (065D)

@stack 065D

Relative finite presentation is local on a finite principal-open cover.
-/

@[expose] public section

universe u v w

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M] [Module A M]

/- Lemma 15.81.8 (065D): if `s` generates the unit ideal, then `M` is finitely presented
relative to `R` exactly when every principal localization `M_f`, for `f ∈ s`, is. -/
@[stacks 065D "Lemma 15.81.8"]
#check
  (Module.FinitePresentationRelativeTo.iff_localizationAway_unitIdeal :
    (s : Finset A) → Ideal.span (s : Set A) = ⊤ →
      (Module.FinitePresentationRelativeTo R A M ↔
        ∀ f : s, Module.FinitePresentationRelativeTo R (Localization.Away f.1)
          (LocalizedModule.Away f.1 M)))
