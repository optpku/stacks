/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap92.«92_27_1_1_Morphism»
public import stacks_project.Chap92.«92_27_1_1_Object»
import StacksCheckRecall
@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Cotangent
universe u
/- 92.27.1.1 (1): the canonical morphism i of ringed topoi. -/
@[stacks 08VK]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.i :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicGeometry.AlgebraicSpace (Spec Λ)),
    RingedSite.ToposHom
      (AlgebraicGeometry.AlgebraicSpace.Cotangent.underlineRingedSite Λ X)
      (AlgebraicGeometry.AlgebraicSpace.Cotangent.ringedSite Λ X))
/- 92.27.1.1 (2): the forgetful projection π of ringed topoi. -/
@[stacks 08VK]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.π :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicGeometry.AlgebraicSpace (Spec Λ)),
    RingedSite.ToposHom
      (AlgebraicGeometry.AlgebraicSpace.Cotangent.underlineRingedSite Λ X)
      (AlgebraicGeometry.AlgebraicSpace.commRingedSiteLift X))
