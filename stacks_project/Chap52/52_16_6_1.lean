module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- 52.16.6.1: define `M` as the inverse limit of the modules of global sections
`H⁰(U, Fₙ)`. -/
@[stacks 0EHD] #check (sectionsLimit :
  (S : AffineAlgebraizationSetup A) →
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) → ModuleCat A)

end AlgebraicGeometry.Scheme.CoherentFormalModules
