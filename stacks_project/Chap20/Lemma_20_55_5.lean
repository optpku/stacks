module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.5 (0F8N): for a complex on which a locally principal regular ideal `I`
acts monomorphically termwise, `I^⊗ i ⊗ (H^i(K) / H^i(K)[I])` is isomorphic to
`H^i(η[I] K)`. -/
@[stacks 0F8N]
#check @IdealSheaf.Eta.tensorPower_torsionQuotient_isomorphic_homology

@[stacks 0F8N "Berthelot-Ogus eta complex"]
#check @IdealSheaf.Eta.complex

@[stacks 0F8N "domain of the ideal-sheaf eta construction"]
#check @IdealSheaf.Eta.Domain

@[stacks 0F8N "degreewise monic ideal action"]
#check @IdealSheaf.IsActionMono.Complex

#check @IdealSheaf.IsRegularPrincipal.isInvertible
