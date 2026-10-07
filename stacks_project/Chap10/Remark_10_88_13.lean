module

import StacksCheckRecall
public import ReasLib.RingTheory.DualNumber.Finiteness
public import ReasLib.RingTheory.Flatness.MittagLeffler.DualNumber

/-!
# Failure of Mittag-Leffler ascent to dual numbers

@stack 05CS
-/

@[expose] public section

universe u v

open scoped DualNumber

section

variable (R : Type u) [CommRing R]

/- Remark 10.88.13 (05CS) (1): the dual-number extension is finite. -/
@[stacks 05CS "(1)"]
#check (DualNumber.finite R : Module.Finite R R[ε])

/- Remark 10.88.13 (05CS) (2): the dual-number extension is finitely presented. -/
@[stacks 05CS "(2)"]
#check (DualNumber.finitePresentation R : Algebra.FinitePresentation R R[ε])

/- Remark 10.88.13 (05CS) (3): finite, finitely presented change of rings need not preserve the
Mittag-Leffler property. -/
@[stacks 05CS "(3)"]
#check (Module.MittagLeffler.DualNumber.exists_not_ascent (R := R) :
  (∃ M₀ : ModuleCat.{v} R, ¬ Module.MittagLeffler R M₀) →
    ∃ M : ModuleCat.{max u v} R[ε],
      Module.MittagLeffler R (ModuleCat.DualNumber.restrict M) ∧
        ¬ Module.MittagLeffler R[ε] M)

end

#check @ModuleCat.DualNumber.ofSquareZero
#check @ModuleCat.DualNumber.ofSquareZeroMap
#check @ModuleCat.DualNumber.restrict
#check @ModuleCat.DualNumber.restrictFunctor
#check @ModuleCat.DualNumber.epsNatTrans
#check @ModuleCat.DualNumber.restrictedEpsNatTrans
#check @ModuleCat.DualNumber.epsQuotient
#check @ModuleCat.DualNumber.EpsQuotient.functor
#check @ModuleCat.DualNumber.EpsQuotient.mkNatTrans
#check @ModuleCat.DualNumber.EpsQuotient.equivQuotSMulTop
#check @ModuleCat.DualNumber.Reconstruction.iso
#check @ModuleCat.DualNumber.Presentation.of
#check @ModuleCat.DualNumber.Presentation.quotientEquiv
#check @Module.MittagLeffler.DualNumber.quotient_eps_overBase
#check @Module.MittagLeffler.DualNumber.ofPresentation_quotient
#check @Module.MittagLeffler.DualNumber.not_ofPresentation
#check @Module.MittagLeffler.DualNumber.exists_not_ascent_of
