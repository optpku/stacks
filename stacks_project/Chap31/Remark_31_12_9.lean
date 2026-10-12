/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Category
import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Monoidal
import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Counterexample
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Remark 31.12.9: on an integral locally Noetherian scheme, reflexive hull is left adjoint to
the inclusion of coherent reflexive modules into coherent modules. -/
@[stacks 0EBH] #check
  (AlgebraicGeometry.Scheme.Modules.reflexiveCohReflectorAdjunction :
    ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X],
      AlgebraicGeometry.Scheme.Modules.reflexiveCohReflector X ⊣
        AlgebraicGeometry.Scheme.Modules.reflexiveCohInclusion X)

#check AlgebraicGeometry.Scheme.Modules.reflexiveCohProperty
#check AlgebraicGeometry.Scheme.Modules.ReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.reflexiveCohForget
#check AlgebraicGeometry.Scheme.Modules.instPreadditiveReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.instHasFiniteBiproductsReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.instHasKernelsReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.reflexiveCohKernelIso
#check AlgebraicGeometry.Scheme.Modules.instHasCokernelsReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.reflexiveCohCokernelIso
#check AlgebraicGeometry.Scheme.Modules.reflexiveTensor
#check AlgebraicGeometry.Scheme.Modules.instMonoidalCategoryReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.instSymmetricCategoryReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.reflexiveCohInternalHom
#check AlgebraicGeometry.Scheme.Modules.reflexiveTensorHomEquiv
#check AlgebraicGeometry.Scheme.Modules.instMonoidalClosedReflexiveCoh
#check AlgebraicGeometry.Scheme.Modules.reflexiveCohDual
#check AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample.scheme
#check AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample.sheaf
#check AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample.rankOneReflexive_sheaf
#check AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample.internalHom_not_iso_reflexiveHull_dual_tensor
#check AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample.reflexiveHull_tensor_dual_not_iso_unit
