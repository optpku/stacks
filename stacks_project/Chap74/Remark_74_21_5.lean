/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal.Properties
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Remark 74.21.5 (1): étale morphisms of algebraic spaces are étale-smooth local
on the source-and-target. -/
@[stacks 0CG3] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.isEtaleSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsEtaleSmoothLocalAtSourceAndTarget (@Etale S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.21.5 (2): morphisms of algebraic spaces that are locally quasi-finite
in the Stacks sense are étale-smooth local on the source-and-target. -/
@[stacks 0CG3] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteType.locallyQuasiFiniteIsEtaleSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsEtaleSmoothLocalAtSourceAndTarget
        (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
          MorphismProperty (AlgebraicSpace S)))

/- Remark 74.21.5 (3): unramified morphisms of algebraic spaces are étale-smooth
local on the source-and-target. -/
@[stacks 0CG3] #check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.isEtaleSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsEtaleSmoothLocalAtSourceAndTarget
        (@Unramified S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.21.5 (4): any morphism property of algebraic spaces that is smooth
local on the source-and-target is a fortiori étale-smooth local. -/
@[stacks 0CG3] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.of_isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      IsEtaleSmoothLocalAtSourceAndTarget P)
