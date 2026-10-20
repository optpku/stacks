module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Morphism
import StacksCheckRecall

@[expose] public section

/- Definition 18.35.4: the naive cotangent complex of a bundled morphism of
commutative ringed-site presentations is the site-level complex of the
canonical structure-sheaf map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 08U0]
#check @RingedSite.Hom.naiveCotangent

#check @RingedSite.Hom.structureSheafUnder
#check @RingedSite.Hom.naiveCotangent_X_negOne
#check @RingedSite.Hom.naiveCotangent_X_zero
#check @RingedSite.Hom.naiveCotangent_d_negOne_zero
