module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Definition 52.16.7: a coherent formal module canonically extends when its associated
global-section pro-object belongs to the essential image of the ambient realization. -/
@[stacks 0EIP] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.CanonicallyExtends :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)), Prop)

end AlgebraicGeometry.Scheme.CoherentFormalModules
