module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Coherence of annihilator sheaves on locally Noetherian schemes

The annihilator of a coherent module on a locally Noetherian scheme is coherent.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The annihilator sheaf of a coherent module on a locally Noetherian scheme is coherent. -/
instance instIsCoherentAnnihilator (ℱ : X.Modules) [ℱ.IsCoherent] :
    (SheafOfModules.annihilator (X := X.toRingedSpace) ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
