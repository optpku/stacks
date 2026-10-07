module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
import StacksCheckRecall

/-!
# Definition 21.45.1

The reusable pseudo-coherence and local strict-perfect approximation API for derived module
sheaves on ringed sites lives in
`ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent`.
-/

@[expose] public section

/- Definition 21.45.1 (08FT): pseudo-coherence for complexes and derived module sheaves is
represented by the canonical complex- and derived-level predicates below. -/
@[stacks 08FT] #check @CochainComplex.IsMPseudoCoherent

#check @CochainComplex.IsPseudoCoherent
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent
#check @RingedSite.Hom.ModuleDerived.IsPseudoCoherent

end
