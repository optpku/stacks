module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Triangulated
import StacksCheckRecall

@[expose] public section

/- Lemma 21.45.4 (1) (08FV): the third vertex of a distinguished triangle inherits the
indicated pseudo-coherence bound. -/
@[stacks 08FV "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.obj₃

/- Lemma 21.45.4 (2) (08FV): the middle vertex inherits the common pseudo-coherence bound. -/
@[stacks 08FV "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.obj₂

/- Lemma 21.45.4 (3) (08FV): the first vertex inherits the shifted pseudo-coherence bound. -/
@[stacks 08FV "(3)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.obj₁

#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.shift_iff
#check @RingedSite.Hom.ModuleDerived.mPseudoCoherent_isTriangulatedClosed₂
#check @RingedSite.Hom.ModuleDerived.mPseudoCoherent_isClosedUnderIsomorphisms
