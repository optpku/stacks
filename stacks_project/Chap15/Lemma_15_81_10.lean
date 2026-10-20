module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Products
import StacksCheckRecall

/-!
Lemma 15.81.10 (0672): both summands of a relatively finitely presented binary product are
finitely presented relative to the base ring.

@stack 0672
-/

@[expose] public section

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w} {M' : Type x}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M'] [Module A M']

/- Lemma 15.81.10 (0672) (1): the left summand is relatively finitely presented. -/
@[stacks 0672 "left product summand"]
#check
  (Module.finitePresentationRelativeTo_left_of_prod :
    Module.FinitePresentationRelativeTo R A (M × M') →
      Module.FinitePresentationRelativeTo R A M)

/- Lemma 15.81.10 (0672) (2): the right summand is relatively finitely presented. -/
@[stacks 0672 "right product summand"]
#check
  (Module.finitePresentationRelativeTo_right_of_prod :
    Module.FinitePresentationRelativeTo R A (M × M') →
      Module.FinitePresentationRelativeTo R A M')
