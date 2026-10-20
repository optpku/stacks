/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChosenFppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.ChangeOfSite
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Preservation of geometric stack properties under enlargement of big sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w uX vX uY vY

namespace AlgebraicGeometry.ChosenBigFppfSite

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

include e hFull hFaithful hSubcanonical hLimits hContinuous hCocontinuous
  hSheafify hSheafify' hKan hFiniteLimits hSheafPullbacks hSheafPullbacks'
  hPullbacks hEqualizers hPostPullbacks hPostEqualizers hSmall

/-- Inverse image along a scheme-compatible enlargement of big fppf sites
preserves representation by the specified scheme, viewed in the larger site. -/
theorem inverseImage_representable_scheme
    (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver)
    (U : 𝒮.bigSite S)
    (hX : IsRepresentedBySheaf 𝒮 S X.toStackOver
      ((𝒮.bigTopology S).sheafifiedRepresentable U)) :
    IsRepresentedBySheaf 𝒯 (inclusion.obj S) I.target
      ((𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
        ((Over.post (X := S) inclusion).obj U)) := sorry

/-- Inverse image of a stack represented by an algebraic-space sheaf is
represented by the actual inverse-image sheaf, which is an algebraic space. -/
theorem inverseImage_representable_algebraicSpace
    (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver)
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (hF : IsAlgebraicSpace F) (hX : IsRepresentedBySheaf 𝒮 S X.toStackOver F) :
    IsAlgebraicSpace
        (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj F) ∧
      IsRepresentedBySheaf 𝒯 (inclusion.obj S) I.target
        (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj F) := sorry

/-- Inverse image along a scheme-compatible enlargement of big fppf sites
preserves algebraicity of stacks. -/
theorem inverseImage_algebraicStack
    (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver)
    (hX : IsAlgebraicStack 𝒮 S X.toStackOver) :
    IsAlgebraicStack 𝒯 (inclusion.obj S) I.target := sorry

/-- Inverse image along a scheme-compatible enlargement of big fppf sites
preserves the Deligne–Mumford property. -/
theorem inverseImage_deligneMumford
    (X : StackOver.Groupoids.{_, _, uX, vX} (𝒮.bigTopology S))
    (I : StackOver.InverseImage.{_, _, _, _, uX, vX, uY, vY}
      (𝒯.bigTopology (inclusion.obj S)) (Over.post (X := S) inclusion) X.toStackOver)
    (hX : IsDeligneMumfordStack 𝒮 S X.toStackOver) :
    IsDeligneMumfordStack 𝒯 (inclusion.obj S) I.target := sorry

end AlgebraicGeometry.ChosenBigFppfSite
