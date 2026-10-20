/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Comparison

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier} (f : T ⟶ S)

/- Lemma 61.12.16 (1): the relocalization morphism factors as `i_f = f_big ∘ i_T`. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.morphism_comp_big_inverseImageIso.{u, v, max u v} f :
    (SmallToBig.morphismOfTopoi f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (Big.morphismOfTopoi f)
        (SmallToBig.morphismOfTopoi (𝟙 T))).inverseImage)

/- Lemma 61.12.16 (2): small pro-étale base change sends `U / S` to
`U ×_S T / T`. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallPullback f : smallSite X S ⥤ smallSite X T)

/- Lemma 61.12.16 (2): small pro-étale base change is continuous. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallPullback_isContinuous f :
    Functor.IsContinuous (smallPullback f) (smallTopology X S)
      (smallTopology X T))

/- Lemma 61.12.16 (2): small pro-étale base change induces the morphism of
topoi `f_small`. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism.{u, v, max u v} f :
    MorphismOfTopoiIn.{max u v, max u v, u, u, max u v}
      (smallTopology X S) (smallTopology X T))

/- Lemma 61.12.16 (2): the direct image along `f_small` evaluates a sheaf on
the base-changed object. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism_pushforward_obj_obj.{u, v, max u v} f :
    ∀ (F : Sheaf (smallTopology X T) (Type (max u v))) (U : smallSite X S),
      ((SmallToBig.smallMorphism.{u, v, max u v} f).pushforward.obj F).1.obj
          (op U) =
        F.1.obj (op ((smallPullback f).obj U)))

/- Lemma 61.12.16 (3): the square of site functors commutes canonically. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallPullback_comp_relocalization_id_iso f :
    smallPullback f ⋙ SmallToBig.relocalizationFunctor (𝟙 T) ≅
      SmallToBig.relocalizationFunctor (𝟙 S) ⋙ Big.pullback f)

/- Lemma 61.12.16 (3): the square of small and big pro-étale morphisms of
topoi commutes, so `f_small ∘ π_T = π_S ∘ f_big`. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism_comp_site_pushforwardIso.{u, v, max u v} f :
    (MorphismOfTopoiIn.comp
        (SmallToBig.smallMorphism.{u, v, max u v} f)
        (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X T)).pushforward ≅
      (MorphismOfTopoiIn.comp
        (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
        (Big.morphismOfTopoi f)).pushforward)

/- Lemma 61.12.16 (4): `f_small = π_S ∘ f_big ∘ i_T`. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism_comp_big_inverseImageIso.{u, v, max u v} f :
    (SmallToBig.smallMorphism.{u, v, max u v} f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
          (Big.morphismOfTopoi f))
        (SmallToBig.morphismOfTopoi (𝟙 T))).inverseImage)

/- Lemma 61.12.16 (4): `f_small = π_S ∘ i_f`. -/
@[stacks 098T] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism_comp_inverseImageIso.{u, v, max u v} f :
    (SmallToBig.smallMorphism.{u, v, max u v} f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
        (SmallToBig.morphismOfTopoi f)).inverseImage)

end AlgebraicGeometry.ChosenBigProetaleSite
