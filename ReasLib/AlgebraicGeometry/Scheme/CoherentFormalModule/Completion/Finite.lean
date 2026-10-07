module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The completed stalk of a coherent formal module is finite over the completed local ring. -/
theorem completedStalk_finite (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (y : S.U) :
    Module.Finite (completedLocalRing S y) (completedStalk S F y) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
