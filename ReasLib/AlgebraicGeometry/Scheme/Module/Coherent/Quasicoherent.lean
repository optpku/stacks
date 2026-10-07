module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Quasi-coherence of coherent scheme modules

This file records the canonical quasi-coherence inference available for
coherent modules on locally Noetherian schemes.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A coherent module on a locally Noetherian scheme is canonically quasi-coherent. -/
instance instIsQuasicoherentOfIsCoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ℱ.IsQuasicoherent :=
  (isCoherent_iff_isQuasicoherent_and_isFiniteType ℱ).mp inferInstance |>.1

end AlgebraicGeometry.Scheme.Modules
