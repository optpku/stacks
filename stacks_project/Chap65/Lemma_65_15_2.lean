/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfSite.FullyFaithful
import StacksCheckRecall

/-!
# Lemma 65.15.2

Enlargement of big fppf sites is fully faithful on algebraic spaces, with
essential image characterized by two smaller-site surjections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite Limits

universe u v

variable (𝒮 𝒯 : ChosenBigFppfSite.{u, v})
variable (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
variable (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
variable [inclusion.Full] [inclusion.Faithful]
variable [PreservesLimitsOfShape WalkingCospan inclusion]
variable [(Over.post (X := S) inclusion).IsContinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [(Over.post (X := S) inclusion).IsCocontinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable [HasPullbacks
  (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasPointwiseRightKanExtension P]
variable [PreservesFiniteLimits
  ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]

/- Lemma 65.15.2. The functor on algebraic spaces is fully faithful, and its
essential image consists exactly of spaces admitting smaller-site surjections
onto the space and the self-fiber-product of its covering map. -/
@[stacks 04W1] #check
  (AlgebraicGeometry.ChosenBigFppfSite.inverseImage_fullyFaithful_essImage
    𝒮 𝒯 inclusion e S :
    (inverseImageFunctor 𝒮 𝒯 inclusion e S).Full ∧
      (inverseImageFunctor 𝒮 𝒯 inclusion e S).Faithful ∧
      ∀ X' : Spaces 𝒯 (inclusion.obj S),
        (inverseImageFunctor 𝒮 𝒯 inclusion e S).essImage X' ↔
          HasSmallSiteSurjections 𝒮 𝒯 inclusion S X'.obj)
