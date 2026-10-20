/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Quadruple.CommonMultiple
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {T : Scheme.{u}}
variable (q q' : RelativeProjQuadruple 𝒜 T)

/- Lemma 27.16.4: compatibility at the least common multiple, equivalence at the product degree,
and compatibility at some positive common multiple are equivalent. -/
@[stacks 01NW] #check
  (AlgebraicGeometry.RelativeProjQuadruple.equivalent_tfae q q' :
    List.TFAE [
      AlgebraicGeometry.RelativeProjQuadruple.CompatibleAtLcm q q',
      AlgebraicGeometry.RelativeProjQuadruple.Equivalent q q',
      AlgebraicGeometry.RelativeProjQuadruple.SomeCommonMultipleCompatible q q'
    ])

end AlgebraicGeometry
