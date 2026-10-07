module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Big
import ReasLib.CategoryTheory.Sites.Over.Topos
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u

/-!
# Lemma 34.5.10

The big smooth morphism is the smooth specialization of the generic slice-site
topos construction. This chapter item checks the complete source-facing
surface directly.
-/

/- Lemma 34.5.10: a scheme morphism induces the bundled morphism of topoi on
the corresponding big smooth sites. -/
@[stacks 04HC] #check
  (AlgebraicGeometry.Scheme.Smooth.Big.morphismOfTopoi :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}}, (T ⟶ S) →
      MorphismOfTopoiIn (AlgebraicGeometry.Scheme.smoothOverTopology S)
        (AlgebraicGeometry.Scheme.smoothOverTopology T))

/- Postcomposition and pullback are the functors between the big smooth slices. -/
section

variable {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)

#check (CategoryTheory.Over.Site.mapFunctor f : Over T ⥤ Over S)

#check (CategoryTheory.Over.Site.pullbackFunctor f : Over S ⥤ Over T)

/- Postcomposition is left adjoint to pullback. -/
#check
  (CategoryTheory.Over.Site.mapPullbackAdjunction f :
    CategoryTheory.Over.Site.mapFunctor f ⊣
      CategoryTheory.Over.Site.pullbackFunctor f)

/- Postcomposition is cocontinuous and continuous, while pullback is continuous. -/
#check
  (inferInstance : Functor.IsCocontinuous
    (CategoryTheory.Over.Site.mapFunctor f)
    (AlgebraicGeometry.Scheme.smoothOverTopology T)
    (AlgebraicGeometry.Scheme.smoothOverTopology S))

#check
  (inferInstance : Functor.IsContinuous
    (CategoryTheory.Over.Site.mapFunctor f)
    (AlgebraicGeometry.Scheme.smoothOverTopology T)
    (AlgebraicGeometry.Scheme.smoothOverTopology S))

#check
  (inferInstance : Functor.IsContinuous
    (CategoryTheory.Over.Site.pullbackFunctor f)
    (AlgebraicGeometry.Scheme.smoothOverTopology S)
    (AlgebraicGeometry.Scheme.smoothOverTopology T))

end

section

variable {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)

/- Inverse image is computed by evaluation on the postcomposed slice object. -/
variable (𝒢 : Sheaf (AlgebraicGeometry.Scheme.smoothOverTopology S) (Type (u + 1)))
  (U : Over T)

#check
  (CategoryTheory.Over.Site.InverseImage.obj_eq.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f 𝒢 U :
      ((CategoryTheory.Over.Site.inverseImage
        (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f).obj
          𝒢).obj.obj (op U) =
        𝒢.obj.obj (op ((CategoryTheory.Over.Site.mapFunctor f).obj U)))

/- The bundled inverse image is the canonical inverse-image functor. -/
#check
  (CategoryTheory.Over.Site.Morphism.inverseImage.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f :
    (AlgebraicGeometry.Scheme.Smooth.Big.morphismOfTopoi f)⁻¹ =
        CategoryTheory.Over.Site.inverseImage
          (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f)

/- The bundled direct-image projection is the canonical direct-image functor. -/
#check
  (CategoryTheory.Over.Site.Morphism.pushforward.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f :
    (AlgebraicGeometry.Scheme.Smooth.Big.morphismOfTopoi f).pushforward =
        CategoryTheory.Over.Site.directImage.{u + 1, u, u + 1}
          (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f)

/- The cocontinuous and continuous-pullback presentations of direct image agree. -/
#check
  (CategoryTheory.Over.Site.Morphism.pushforwardPresentation.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f :
    (AlgebraicGeometry.Scheme.Smooth.Big.morphismOfTopoi f).pushforward ≅
        (CategoryTheory.Over.Site.pullbackFunctor f).sheafPushforwardContinuous
          (Type (u + 1)) (AlgebraicGeometry.Scheme.smoothOverTopology S)
          (AlgebraicGeometry.Scheme.smoothOverTopology T))

/- Direct image is computed by evaluation on the pullback slice object. -/
variable (ℱ : Sheaf (AlgebraicGeometry.Scheme.smoothOverTopology T) (Type (u + 1)))
  (V : Over S)

#check
  (CategoryTheory.Over.Site.DirectImage.obj_eq.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f ℱ V :
      ((CategoryTheory.Over.Site.directImage.{u + 1, u, u + 1}
        (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f).obj
          ℱ).obj.obj (op V) =
        ℱ.obj.obj (op ((CategoryTheory.Over.Site.pullbackFunctor f).obj V)))

end

/- Lower shriek is left adjoint to the bundled inverse image. -/
section

variable {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
variable [HasWeakSheafify (AlgebraicGeometry.Scheme.smoothOverTopology S)
  (Type (u + 1))]

#check
  (CategoryTheory.Over.Site.LowerShriek.adjunction_viaMorphism.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f :
    CategoryTheory.Over.Site.lowerShriek
        (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f ⊣
      (AlgebraicGeometry.Scheme.Smooth.Big.morphismOfTopoi f)⁻¹)

/- Lower shriek preserves pullbacks and equalizers. -/
#check
  (CategoryTheory.Over.Site.LowerShriek.preservesPullbacks.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f :
    PreservesLimitsOfShape WalkingCospan
      (CategoryTheory.Over.Site.lowerShriek
        (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f))

#check
  (CategoryTheory.Over.Site.LowerShriek.preservesEqualizers.{u + 1, u, u + 1}
      (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f :
    PreservesLimitsOfShape WalkingParallelPair
      (CategoryTheory.Over.Site.lowerShriek
        (AlgebraicGeometry.Scheme.grothendieckTopology @AlgebraicGeometry.Smooth) f))

end
