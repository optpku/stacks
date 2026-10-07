module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InternalHom.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Quasicoherence of internal Hom

Internal Hom from a finitely presented module sheaf to a quasicoherent module sheaf is
quasicoherent.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The internal Hom from a finitely presented module sheaf to a quasicoherent module sheaf is
quasicoherent. -/
@[instance]
theorem isQuasicoherent_internalHom (ℱ 𝒢 : X.Modules)
    [ℱ.IsFinitePresentation] [𝒢.IsQuasicoherent] :
    (internalHom ℱ 𝒢).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
