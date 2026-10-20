/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfSite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

variable (𝒮 𝒯 : ChosenBigFppfSite.{u, v})
variable (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
variable (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
variable [inclusion.Full] [inclusion.Faithful]
variable [PreservesLimitsOfShape WalkingCospan inclusion]
variable [(Over.post (X := S) inclusion).IsContinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable [HasPullbacks
  (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]

/- Lemma 65.15.1 (1): inverse image along the inclusion of two big fppf sites
preserves representability. The compatibility isomorphism e identifies the image
object with the same underlying scheme over the image of S. -/
@[stacks 03FP] #check
  (CategoryTheory.Functor.SheafifiedRepresentable.pullbackIso
    (Over.post (X := S) inclusion) (𝒮.bigTopology S)
    (𝒯.bigTopology (inclusion.obj S)) :
    ∀ U : Over S,
      (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
          ((Over.post (X := S) inclusion).obj U) ≅
        ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
          (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj
          ((𝒮.bigTopology S).sheafifiedRepresentable U))

variable (F : Sheaf (𝒮.bigTopology S) (Type (max u v)))
variable [ChosenBigFppfSite.IsAlgebraicSpace F]

/- Lemma 65.15.1 (2): inverse image along a scheme-compatible inclusion of two
big fppf sites sends an algebraic-space sheaf over S to an algebraic-space sheaf
over the same scheme in the larger site. -/
@[stacks 03FP] #check
  (AlgebraicGeometry.ChosenBigFppfSite.inverseImage_isAlgebraicSpace
    𝒮 𝒯 inclusion e S F :
    ChosenBigFppfSite.IsAlgebraicSpace
      (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj F))
