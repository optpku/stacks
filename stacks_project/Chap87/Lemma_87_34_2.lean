/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite
import StacksCheckRecall

/-!
# Lemma 87.34.2

A morphism of formal algebraic spaces induces a morphism of étale sites of
algebraic spaces over the reductions, hence a morphism of small étale topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.34.2 (1): a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` induces a continuous functor `Y_spaces,étale ⥤ X_spaces,étale`,
hence a morphism of sites
`f_spaces,étale : X_spaces,étale ⟶ Y_spaces,étale`. -/
@[stacks 0DEC] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.spacesEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y),
      IsMorphismOfSites (ReductionData.spacesEtaleTopology RY)
        (ReductionData.spacesEtaleTopology RX) (ReductionData.spacesEtalePullback RX RY f))

/- Lemma 87.34.2 (2): the rule `f ↦ f_spaces,étale` is compatible with
composition, via the pullback-composition isomorphism for the actual composite
of formal-space morphisms, in the sense of Sites, Definition 7.14.5. -/
@[stacks 0DEC] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.spacesEtalePullbackComp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [IsFormalAlgebraicSpace Z]
      (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
      (f : X ⟶ Y) (g : Y ⟶ Z),
      ReductionData.spacesEtalePullback RX RZ (f ≫ g) ≅
        ReductionData.spacesEtalePullback RY RZ g ⋙ ReductionData.spacesEtalePullback RX RY f)

/- Lemma 87.34.2 (3): transporting the topos morphism of `f_spaces,étale` along
equation 87.34.1.1 yields `f_small : Sh(X_étale) ⟶ Sh(Y_étale)`, compatible
with composition. -/
@[stacks 0DEC] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.smallEtaleMorphismOfTopoi :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      (RX : ReductionData X) (RY : ReductionData Y),
      (X ⟶ Y) →
        MorphismOfTopoiIn (ReductionData.smallEtaleTopology RY)
          (ReductionData.smallEtaleTopology RX))

#check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.smallEtaleMorphismOfTopoiComp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [IsFormalAlgebraicSpace Z]
      (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
      (f : X ⟶ Y) (g : Y ⟶ Z),
      (ReductionData.smallEtaleMorphismOfTopoi RX RZ (f ≫ g)).inverseImage ≅
        ((ReductionData.smallEtaleMorphismOfTopoi RY RZ g).comp
          (ReductionData.smallEtaleMorphismOfTopoi RX RY f)).inverseImage)

