/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules
namespace IsLocallyProjective

/-- If `T` is affine, `F` and `G` are quasi-coherent `T`-modules, and `F` is locally
projective, then the first cohomology of `internalHom F G` vanishes. -/
@[stacks 0D0E]
theorem internalHom_firstCohomology_isZero
    {T : Scheme.{u}} [IsAffine T]
    (F G : T.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [IsLocallyProjective F] :
    IsZero (cohomology (internalHom F G) 1) := sorry

end IsLocallyProjective
end Scheme.Modules
end AlgebraicGeometry
