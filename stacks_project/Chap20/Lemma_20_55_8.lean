module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Reduction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.8 (0GT9): for every `M : D(𝒪_X)`, reduction of `Lη_I M` modulo a
locally principal regular ideal is isomorphic to the derived image of the canonical Bockstein
cohomology complex `H^•(M / I)`. -/
@[stacks 0GT9]
#check @IdealSheaf.Eta.Derived.tensorQuotient_isomorphic_bockstein

@[stacks 0GT8 "Bockstein complex"]
#check @IdealSheaf.Bockstein.complex

@[stacks 0GT8 "Bockstein differential"]
#check @IdealSheaf.Bockstein.d

#check @IdealSheaf.Bockstein.term
#check @IdealSheaf.Bockstein.triangle
#check @IdealSheaf.Power.row_shortExact
#check @IdealSheaf.Power.piece
#check @IdealSheaf.IsRegularPrincipal.isInvertible
