module

import ReasLib.RingTheory.RingHom.FinitePresentation.ModuleOverLocalization
import StacksCheckRecall

universe u v w

/- 38.25.6.1: Fix a finitely presented ring homomorphism `f : A →+* B`, a
multiplicative subset `S : Submonoid B`, and a finitely presented
`Localization S`-module `N`. -/
@[stacks 0AT6]
#check (RingHom.FinitePresentation.withModuleOverLocalization :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (S : Submonoid B) (N : Type w) [AddCommGroup N]
    [Module (Localization S) N], Prop)
