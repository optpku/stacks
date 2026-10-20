module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesToBig

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Lemma 73.4.11 (1): the relocalization morphism factors as `i_f = f_big ∘ i_Y`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.morphismCompBigIso f :
    (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} f).inverseImage ≅
      (MorphismOfTopoiIn.comp (Etale.Big.morphismOfTopoi f)
        (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} (𝟙 Y))).inverseImage)

/- Lemma 73.4.11 (2): spaces-étale base change sends `U / X` to `U ×_X Y / Y`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback f : spacesEtaleSite X ⥤ spacesEtaleSite Y)

/- Lemma 73.4.11 (3): spaces-étale base change is continuous. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback_isContinuous f :
    Functor.IsContinuous (spacesEtalePullback f) (spacesEtaleTopology X)
      (spacesEtaleTopology Y))

/- Lemma 73.4.11 (4): spaces-étale base change induces the morphism of sites
`f_spaces,étale`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback_isMorphismOfSites f :
    IsMorphismOfSites (spacesEtaleTopology X) (spacesEtaleTopology Y)
      (spacesEtalePullback f))

/- Lemma 73.4.11 (5): spaces-étale base change induces the morphism of topoi
whose transport defines `f_small`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtaleMorphismOfTopoi f :
    MorphismOfTopoiIn (spacesEtaleTopology X) (spacesEtaleTopology Y))

/- Lemma 73.4.11 (6): the direct image along `f_small` evaluates a sheaf on the
base-changed object. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.spacesEtaleMorphismOfTopoi_pushforward_obj_obj f :
    ∀ (F : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) (U : spacesEtaleSite X),
      ((spacesEtaleMorphismOfTopoi f).pushforward.obj F).1.obj (op U) =
        F.1.obj (op ((spacesEtalePullback f).obj U)))

/- Lemma 73.4.11 (7): the square of spaces-étale and big étale morphisms of
topoi commutes, so `f_small ∘ π_Y = π_X ∘ f_big`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.spacesEtaleMorphismOfTopoiCompSiteIso f :
    (MorphismOfTopoiIn.comp (spacesEtaleMorphismOfTopoi f)
        (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} Y)).inverseImage ≅
      (MorphismOfTopoiIn.comp (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X)
        (Etale.Big.morphismOfTopoi f)).inverseImage)

/- Lemma 73.4.11 (8): `f_small = π_X ∘ f_big ∘ i_Y`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.spacesEtaleMorphismOfTopoiCompBigIso f :
    (spacesEtaleMorphismOfTopoi f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X)
          (Etale.Big.morphismOfTopoi f))
        (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} (𝟙 Y))).inverseImage)

/- Lemma 73.4.11 (9): `f_small = π_X ∘ i_f`. -/
@[stacks 0DF6] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.spacesEtaleMorphismOfTopoiCompIso f :
    (spacesEtaleMorphismOfTopoi f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X)
        (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} f)).inverseImage)

/- The canonical inclusion and base-change functors form the underlying site square. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.pullbackForgetIso f :
    MorphismProperty.Over.forget (@Etale S) ⊤ X ⋙ Over.pullback f ≅
      spacesEtalePullback f ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ Y)

/- The associated small étale geometric morphism and its restriction-extension transport. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi f :
    MorphismOfTopoiIn (smallEtaleTopology X) (smallEtaleTopology Y))

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi_eq f :
    smallEtaleMorphismOfTopoi f =
      (smallEtaleInclusionInverseMorphismOfTopoi X).comp
        ((spacesEtaleMorphismOfTopoi f).comp (smallEtaleInclusionMorphismOfTopoi Y)))

end AlgebraicGeometry.AlgebraicSpace
