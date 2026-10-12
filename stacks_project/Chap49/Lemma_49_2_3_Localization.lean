/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Localization

/-! Compatibility checks for the relative-dualizing localization API. -/

#check Algebra.RelativeDualizingModule.awayFactorMap
#check Algebra.RelativeDualizingModule.awayFactorMap_comp
#check Algebra.RelativeDualizingModule.awayFactorMap_isScalarTower
#check Algebra.RelativeDualizingModule.quasiFiniteAwayBase
#check Algebra.RelativeDualizingModule.quasiFiniteAwayTarget
#check Algebra.RelativeDualizingModule.finiteAwayBase
#check Algebra.RelativeDualizingModule.openAwayBase
#check Algebra.RelativeDualizingModule.openAwayTarget
#check Algebra.RelativeDualizingModule.awayBaseIso
#check Algebra.RelativeDualizingModule.awayBaseIso_hom_tmul
#check Algebra.RelativeDualizingModule.awayTargetIso
#check Algebra.RelativeDualizingModule.awayTargetIso_hom_mk
#check Algebra.RelativeDualizingModule.awayIso
#check Algebra.RelativeDualizingModule.awayIso_eq
