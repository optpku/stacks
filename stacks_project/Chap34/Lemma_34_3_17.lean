module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
import stacks_project.Chap34.Lemma_34_3_12
import stacks_project.Chap34.Lemma_34_3_14

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- The big-Zariski morphism of topoi associated to a scheme morphism. -/
abbrev bigZariskiMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn S.bigZariskiTopology T.bigZariskiTopology :=
  Zariski.Big.morphismOfTopoi f

/-- The small-Zariski morphism of topoi associated to a scheme morphism. -/
abbrev smallZariskiMorphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn S.smallZariskiTopology T.smallZariskiTopology :=
  Zariski.SmallToBig.smallMorphism f

/- Lemma 34.3.17: the relocalization morphism associated to `f : T ⟶ S` is the
composite of the big-Zariski morphism of `f` with the relocalization at `T`. -/
@[stacks 0211] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.morphism_eq_comp_big :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      Zariski.SmallToBig.morphismOfTopoi f =
        MorphismOfTopoiIn.comp (Zariski.Big.morphismOfTopoi f)
          (Zariski.SmallToBig.morphismOfTopoi (𝟙 T)))

#check
  (AlgebraicGeometry.Scheme.smallZariskiPullback_isContinuous :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S),
      Functor.IsContinuous (smallZariskiPullback f)
        S.smallZariskiTopology T.smallZariskiTopology)

#check
  (AlgebraicGeometry.Scheme.smallZariskiPullback_isMorphismOfSites :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S),
      IsMorphismOfSites S.smallZariskiTopology T.smallZariskiTopology
        (smallZariskiPullback f))

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_eq_induced :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      Zariski.SmallToBig.smallMorphism f =
        IsMorphismOfSites.toMorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
          (smallZariskiPullback f))

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_inverseImageIsoUsual :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      (Zariski.SmallToBig.smallMorphism f)⁻¹ ⋙
          (smallZariskiTypeSheafEquiv T).functor ≅
        (smallZariskiTypeSheafEquiv S).functor ⋙
          (TopologicalSpace.Opens.map (TopCat.ofHom f.base.hom)).sheafPullback
            (Type (u + 1)) (Opens.grothendieckTopology (S : TopCat))
            (Opens.grothendieckTopology (T : TopCat)))

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_pushforwardIsoUsual :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      (Zariski.SmallToBig.smallMorphism f) _* ⋙
          (smallZariskiTypeSheafEquiv S).functor ≅
        (smallZariskiTypeSheafEquiv T).functor ⋙
          TopCat.Sheaf.pushforward (Type (u + 1)) f.base)

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_pushforward_obj_obj :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))]
      (ℱ : Sheaf T.smallZariskiTopology (Type (u + 1)))
      (U : S.smallZariskiSite),
      (((Zariski.SmallToBig.smallMorphism f) _*).obj ℱ).1.obj (op U) =
        ℱ.1.obj (op ((smallZariskiPullback f).obj U)))

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_comp_site :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      MorphismOfTopoiIn.comp (Zariski.SmallToBig.smallMorphism f)
          (Zariski.SmallToBig.siteMorphismOfTopoi T) =
        MorphismOfTopoiIn.comp (Zariski.SmallToBig.siteMorphismOfTopoi S)
          (Zariski.Big.morphismOfTopoi f))

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_eq_comp_big :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      Zariski.SmallToBig.smallMorphism f =
        MorphismOfTopoiIn.comp
          (MorphismOfTopoiIn.comp (Zariski.SmallToBig.siteMorphismOfTopoi S)
            (Zariski.Big.morphismOfTopoi f))
          (Zariski.SmallToBig.morphismOfTopoi (𝟙 T)))

#check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.smallMorphism_eq_comp :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallZariskiTopology (Type (u + 1))],
      Zariski.SmallToBig.smallMorphism f =
        MorphismOfTopoiIn.comp (Zariski.SmallToBig.siteMorphismOfTopoi S)
          (Zariski.SmallToBig.morphismOfTopoi f))

end AlgebraicGeometry.Scheme
