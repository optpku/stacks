module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Relative
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.7.2

The relative fibre-product adjunction and its invertible counit are recalled from their canonical
change-of-rings owner.

@stack 08KM
-/

/- Lemma 15.7.2 (1): relative scalar extension is left adjoint to the fibre-product module
functor. -/
@[stacks 08KM "Lemma 15.7.2 (1): relative fibre-product adjunction"]
#check @FiberProductBaseChangeSituation.relativeAdjunction

/- Lemma 15.7.2 (2): the right-adjoint/base-change composite is naturally isomorphic to the
identity. -/
@[stacks 08KM "Lemma 15.7.2 (2): relative counit isomorphism"]
#check @FiberProductBaseChangeSituation.relativeCounitIso

#check @FiberProductBaseChangeSituation.relativeRightAdjoint
#check @FiberProductBaseChangeSituation.relativeCounit_isIso

end
