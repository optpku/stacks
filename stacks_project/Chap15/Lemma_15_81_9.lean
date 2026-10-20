module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Exact
import StacksCheckRecall

/-!
Lemma 15.81.9 (0671): relative finite presentation in a short exact sequence.

@stack 0671
-/

@[expose] public section

universe u v w x y

variable {R : Type u} {A : Type v}
variable {M' : Type w} {M : Type x} {M'' : Type y}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M'] [Module A M']
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M''] [Module A M'']

/- Lemma 15.81.9 (0671) (1): relative finite presentation is closed under extensions. -/
@[stacks 0671 "relative finite presentation is closed under extensions"]
#check
  (Module.finitePresentationRelativeTo_of_shortExact :
    (f : M' →ₗ[A] M) → (g : M →ₗ[A] M'') →
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      Module.FinitePresentationRelativeTo R A M' →
      Module.FinitePresentationRelativeTo R A M'' →
      Module.FinitePresentationRelativeTo R A M)

/- Lemma 15.81.9 (0671) (2): a finite kernel source and relatively finitely presented middle
term give a relatively finitely presented quotient. -/
@[stacks 0671 "relative finite presentation of a quotient in a short exact sequence"]
#check
  (Module.finitePresentationRelativeTo_quotient_of_shortExact :
    (f : M' →ₗ[A] M) → (g : M →ₗ[A] M'') →
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      Module.Finite A M' → Module.FinitePresentationRelativeTo R A M →
      Module.FinitePresentationRelativeTo R A M'')
