/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Localization

/-!
# Intermediate Presentations for Generic Flatness

This leaf packages the finite-presentation descent through an intermediate
algebra over a principal localization.  Polynomial presentations are one
important specialization, but the composition argument itself is independent
of the chosen presentation algebra.

@stack 051T
-/

@[expose] public section

universe u v w x

namespace GenericFlatness.LocalizationCondition

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module S M]

/-- Tag `051T`: an intermediate finitely presented algebra presentation of the target
localization, together with finite presentation of the target-localized module and freeness for
the canonical relative principal-localization actions, gives the generic-flatness localization
condition at `f`. -/
@[stacks 051T "generic-flatness intermediate localization condition"]
theorem ofIntermediate
    {A : Type x} [CommRing A] (f : R)
    [Algebra (Localization.Away f) A]
    [Algebra A (Localization.Away (algebraMap R S f))]
    (h_algebra_tower :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra (R := R) (S := S) f
      IsScalarTower (Localization.Away f) A (Localization.Away (algebraMap R S f)))
    [Algebra.FinitePresentation (Localization.Away f) A]
    [Algebra.FinitePresentation A (Localization.Away (algebraMap R S f))]
    [Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    (h_free_algebra :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra (R := R) (S := S) f
      Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f)))
    (h_free_module :
      letI : Module (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) :=
        Localization.Away.Relative.algebraMapModule (R := R) (S := S) (M := M) f
      Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)) :
    LocalizationCondition R S M f := sorry

end GenericFlatness.LocalizationCondition
