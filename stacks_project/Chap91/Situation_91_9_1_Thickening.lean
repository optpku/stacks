/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening

/-!
# Compatibility checks for ringed-topos thickening API

The reusable declarations are provided by the mathematical owner. This module preserves the
historical import path through typed checks of the public API.
-/

#check RingedSite.ToposHom.kernelMap
#check RingedSite.ToposHom.kernelIdeal
#check RingedSite.ToposHom.ker
#check RingedSite.ToposHom.kernelIdeal_ι
#check RingedSite.ToposHom.kernelIdeal_ι_comp_kernelMap
#check RingedSite.ToposHom.IsLocallyNilpotent
#check RingedSite.ToposHom.isLocallyNilpotent_iff
#check RingedSite.ToposHom.kernel_isSquareZero
#check RingedSite.ToposHom.kernel_isSquareZero_iff
#check RingedSite.ToposHom.IsThickening
#check RingedSite.ToposHom.isThickening_iff
#check RingedSite.ToposHom.IsFirstOrderThickening
#check RingedSite.ToposHom.isFirstOrderThickening_iff
#check RingedSite.ToposHom.idealModule
#check RingedSite.ToposHom.idealModule_eq
