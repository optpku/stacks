/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfSite
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap78.Lemma_78_28_1
public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Theorem_94_17_3

/-!
# Lemma 94.18.1

Enlarging a big fppf site preserves representation by the same scheme,
representation by the inverse-image algebraic space, algebraicity, and the
Deligne–Mumford property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

universe u v w uX vX uY vY

variable (𝒮 𝒯 : ChosenBigFppfSite.{u, v})
variable (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
variable (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
variable [hFull : inclusion.Full] [hFaithful : inclusion.Faithful]
variable [hSubcanonical : (𝒮.bigTopology S).Subcanonical]
variable [hLimits : PreservesLimitsOfShape WalkingCospan inclusion]
variable [hContinuous : (Over.post (X := S) inclusion).IsContinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [hCocontinuous : (Over.post (X := S) inclusion).IsCocontinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hSheafify' : HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
variable [hKan : ∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
variable [hFiniteLimits : PreservesFiniteLimits
  ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]
variable [hSheafPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable [hSheafPullbacks' : HasPullbacks
  (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]
variable [hPullbacks : HasPullbacks (Over S)] [hEqualizers : HasEqualizers (Over S)]
variable [hPostPullbacks : PreservesLimitsOfShape WalkingCospan (Over.post (X := S) inclusion)]
variable [hPostEqualizers : PreservesLimitsOfShape WalkingParallelPair
  (Over.post (X := S) inclusion)]
variable [hSmall : Small.{w} (Over (inclusion.obj S))]

/- Lemma 94.18.1 (1): Inverse image along a scheme-compatible enlargement of big fppf sites
preserves representation by the specified scheme, viewed in the larger site. -/
@[stacks 04X2] #check
  (AlgebraicGeometry.ChosenBigFppfSite.inverseImage_representable_scheme 𝒮 𝒯 inclusion e S :
    ∀ (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver),
      ∀ (U : 𝒮.bigSite S),
      IsRepresentedBySheaf 𝒮 S X.toStackOver
        ((𝒮.bigTopology S).sheafifiedRepresentable U) →
      IsRepresentedBySheaf 𝒯 (inclusion.obj S) I.target
      ((𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
        ((Over.post (X := S) inclusion).obj U)))

/- Lemma 94.18.1 (2): Inverse image of a stack represented by an algebraic-space sheaf is
represented by the actual inverse-image sheaf, which is an algebraic space. -/
@[stacks 04X2] #check
  (AlgebraicGeometry.ChosenBigFppfSite.inverseImage_representable_algebraicSpace 𝒮 𝒯 inclusion e S :
    ∀ (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver),
      ∀ (F : Sheaf (𝒮.bigTopology S) (Type (max u v))),
      IsAlgebraicSpace F → IsRepresentedBySheaf 𝒮 S X.toStackOver F →
      IsAlgebraicSpace
        (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj F) ∧
      IsRepresentedBySheaf 𝒯 (inclusion.obj S) I.target
        (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj F))

/- Lemma 94.18.1 (3): Inverse image along a scheme-compatible enlargement of big fppf sites
preserves algebraicity of stacks. -/
@[stacks 04X2] #check
  (AlgebraicGeometry.ChosenBigFppfSite.inverseImage_algebraicStack 𝒮 𝒯 inclusion e S :
    ∀ (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver),
      IsAlgebraicStack 𝒮 S X.toStackOver →
      IsAlgebraicStack 𝒯 (inclusion.obj S) I.target)

/- Lemma 94.18.1 (4): Inverse image along a scheme-compatible enlargement of big fppf sites
preserves the Deligne–Mumford property. -/
@[stacks 04X2] #check
  (AlgebraicGeometry.ChosenBigFppfSite.inverseImage_deligneMumford 𝒮 𝒯 inclusion e S :
    ∀ (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver),
      IsDeligneMumfordStack 𝒮 S X.toStackOver →
      IsDeligneMumfordStack 𝒯 (inclusion.obj S) I.target)

