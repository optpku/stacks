module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.FiniteExtension
import StacksCheckRecall

/-!
# Lemma 15.81.3 (05H0)

@stack 05H0
-/

@[expose] public section

universe u v w x

/- Lemma 15.81.3 (05H0): finite scalar extension preserves and reflects relative finite
presentation. -/
@[stacks 05H0 "Lemma 15.81.3"]
#check fun {R : Type u} {A : Type v} {B : Type w} {M : Type x}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Algebra.FiniteType R A] [Module.Finite A B] ↦
  (Module.finitePresentationRelativeTo_iff_of_finite :
    Module.FinitePresentationRelativeTo R A M ↔
      Module.FinitePresentationRelativeTo R B M)
