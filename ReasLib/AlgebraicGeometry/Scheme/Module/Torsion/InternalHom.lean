/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion

/-!
# Torsion-freeness of internal Hom

Internal Hom from a finitely presented module sheaf to a quasicoherent torsion-free module
sheaf on an integral scheme is torsion-free.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- On an integral scheme, the internal Hom from a finitely presented module sheaf to a
quasicoherent torsion-free module sheaf is torsion-free. -/
@[instance]
theorem isTorsionFree_internalHom (ℱ 𝒢 : X.Modules)
    [ℱ.IsFinitePresentation] [𝒢.IsQuasicoherent] [IsTorsionFree 𝒢] :
    IsTorsionFree (internalHom ℱ 𝒢) := sorry

end AlgebraicGeometry.Scheme.Modules
