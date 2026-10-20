/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace
import StacksCheckRecall

/-!
# Lemma 87.34.3

An étale morphism of formal algebraic spaces, representable by algebraic spaces,
induces a cocontinuous and continuous functor of small étale sites. Its associated
inverse image agrees with that of the canonical morphism of small étale topoi.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.34.3: étale postcomposition on the small étale sites of reductions is cocontinuous. -/
@[stacks 0DED] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.etaleRestriction_isCocontinuous :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [Etale f],
      (ReductionData.etaleRestriction RX RY f).IsCocontinuous
        (AlgebraicSpace.smallEtaleTopology RX.space)
        (AlgebraicSpace.smallEtaleTopology RY.space))

#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.etaleRestriction_isContinuous :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [Etale f],
    (ReductionData.etaleRestriction RX RY f).IsContinuous
      (AlgebraicSpace.smallEtaleTopology RX.space)
      (AlgebraicSpace.smallEtaleTopology RY.space))

#check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [Etale f],
      (ReductionData.smallEtaleMorphismOfTopoi RX RY f).inverseImage ≅
        (ReductionData.etaleRestriction RX RY f).sheafPullbackCocontinuous (Type (u + 1))
          (AlgebraicSpace.smallEtaleTopology RX.space)
          (AlgebraicSpace.smallEtaleTopology RY.space))
