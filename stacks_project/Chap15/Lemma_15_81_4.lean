/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Localization
import StacksCheckRecall

/-!
Lemma 15.81.4 (065A): localization of a relatively finitely presented module.

@stack 065A
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] {f : R}
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable [Algebra.FiniteType (Localization.Away f) A]
variable {g : A} {M : Type w} [AddCommGroup M] [Module A M]

/- Lemma 15.81.4 (065A): localizing over the target turns relative finite presentation over
`Localization.Away f` into relative finite presentation over `R`. -/
@[stacks 065A "relative finite presentation after localization"]
#check
  (Module.finitePresentationRelativeTo_localizationAway_from_localizedBase :
    Module.FinitePresentationRelativeTo (Localization.Away f) A M →
      Module.FinitePresentationRelativeTo R (Localization.Away g)
        (LocalizedModule.Away g M))
