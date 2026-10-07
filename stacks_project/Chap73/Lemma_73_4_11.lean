module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_4_11_Comparison

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
  (Etale.SpacesToBig.morphism_eq_comp_big f :
    Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} f =
      MorphismOfTopoiIn.comp (Etale.Big.morphismOfTopoi f)
        (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} (𝟙 Y)))

/- Lemma 73.4.11 (2): spaces-étale base change sends `U / X` to `U ×_X Y / Y`. -/
@[stacks 0DF6] #check
  (spacesEtalePullback f : spacesEtaleSite X ⥤ spacesEtaleSite Y)

/- Lemma 73.4.11 (3): spaces-étale base change is continuous. -/
@[stacks 0DF6] #check
  (spacesEtalePullback_isContinuous f :
    Functor.IsContinuous (spacesEtalePullback f) (spacesEtaleTopology X)
      (spacesEtaleTopology Y))

/- Lemma 73.4.11 (4): spaces-étale base change induces the morphism of sites
`f_spaces,étale`. -/
@[stacks 0DF6] #check
  (spacesEtalePullback_isMorphismOfSites f :
    IsMorphismOfSites (spacesEtaleTopology X) (spacesEtaleTopology Y)
      (spacesEtalePullback f))

/- Lemma 73.4.11 (5): spaces-étale base change induces the morphism of topoi
`f_small`. -/
@[stacks 0DF6] #check
  (spacesEtaleMorphismOfTopoi f :
    MorphismOfTopoiIn (spacesEtaleTopology X) (spacesEtaleTopology Y))

/- Lemma 73.4.11 (6): the direct image along `f_small` evaluates a sheaf on the
base-changed object. -/
@[stacks 0DF6] #check
  (Etale.SpacesToBig.spacesEtaleMorphismOfTopoi_pushforward_obj_obj f :
    ∀ (F : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) (U : spacesEtaleSite X),
      ((spacesEtaleMorphismOfTopoi f).pushforward.obj F).1.obj (op U) =
        F.1.obj (op ((spacesEtalePullback f).obj U)))

/- Lemma 73.4.11 (7): the square of spaces-étale and big étale morphisms of
topoi commutes, so `f_small ∘ π_Y = π_X ∘ f_big`. -/
@[stacks 0DF6] #check
  (Etale.SpacesToBig.spacesEtaleMorphismOfTopoi_comp_site f :
    MorphismOfTopoiIn.comp (spacesEtaleMorphismOfTopoi f)
        (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} Y) =
      MorphismOfTopoiIn.comp (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X)
        (Etale.Big.morphismOfTopoi f))

/- Lemma 73.4.11 (8): `f_small = π_X ∘ f_big ∘ i_Y`. -/
@[stacks 0DF6] #check
  (Etale.SpacesToBig.spacesEtaleMorphismOfTopoi_eq_comp_big f :
    spacesEtaleMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X)
          (Etale.Big.morphismOfTopoi f))
        (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} (𝟙 Y)))

/- Lemma 73.4.11 (9): `f_small = π_X ∘ i_f`. -/
@[stacks 0DF6] #check
  (Etale.SpacesToBig.spacesEtaleMorphismOfTopoi_eq_comp f :
    spacesEtaleMorphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X)
        (Etale.SpacesToBig.morphismOfTopoi.{u, u + 1} f))

end AlgebraicGeometry.AlgebraicSpace
