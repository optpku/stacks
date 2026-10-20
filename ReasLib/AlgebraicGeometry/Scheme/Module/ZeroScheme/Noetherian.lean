/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

/-!
# Noetherian zero schemes

This file supplies finiteness instances for the zero scheme of a section on a locally
Noetherian scheme.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- The zero scheme of a section on a locally Noetherian scheme is locally Noetherian. -/
instance zeroSchemeIsLocallyNoetherian [IsLocallyNoetherian Y]
    (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) : IsLocallyNoetherian (zeroScheme ℒ s) := sorry

/-- The canonical immersion of a zero scheme into a locally Noetherian scheme is quasi-compact. -/
instance zeroSchemeιQuasiCompact [IsLocallyNoetherian Y]
    (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) : QuasiCompact (zeroSchemeι ℒ s) := sorry

end AlgebraicGeometry.Scheme.Modules
