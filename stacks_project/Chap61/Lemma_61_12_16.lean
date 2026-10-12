/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap61.Lemma_61_12_16_Comparison
public import stacks_project.Chap61.Lemma_61_12_16_Pullback

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
  (SmallToBig.morphism_eq_comp_big.{u, v, max u v} f :
    SmallToBig.morphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (Big.morphismOfTopoi f)
        (SmallToBig.morphismOfTopoi (𝟙 T)))

/- Lemma 61.12.16 (2): small pro-étale base change sends `U / S` to
`U ×_S T / T`. -/
@[stacks 098T] #check
  (smallPullback f : smallSite X S ⥤ smallSite X T)

/- Lemma 61.12.16 (3): small pro-étale base change is continuous. -/
@[stacks 098T] #check
  (smallPullback_isContinuous f :
    Functor.IsContinuous (smallPullback f) (smallTopology X S)
      (smallTopology X T))

/- Lemma 61.12.16 (4): small pro-étale base change induces the morphism of
topoi `f_small`. -/
@[stacks 098T] #check
  (SmallToBig.smallMorphism.{u, v, max u v} f :
    MorphismOfTopoiIn.{max u v, max u v, v, v, max u v}
      (smallTopology X S) (smallTopology X T))

/- Lemma 61.12.16 (5): the direct image along `f_small` evaluates a sheaf on
the base-changed object. -/
@[stacks 098T] #check
  (SmallToBig.smallMorphism_pushforward_obj_obj.{u, v, max u v} f :
    ∀ (F : Sheaf (smallTopology X T) (Type (max u v))) (U : smallSite X S),
      ((SmallToBig.smallMorphism.{u, v, max u v} f).pushforward.obj F).1.obj
          (op U) =
        F.1.obj (op ((smallPullback f).obj U)))

/- Lemma 61.12.16 (6): the square of small and big pro-étale morphisms of
topoi commutes, so `f_small ∘ π_T = π_S ∘ f_big`. -/
@[stacks 098T] #check
  (SmallToBig.smallMorphism_comp_site.{u, v, max u v} f :
    MorphismOfTopoiIn.comp
        (SmallToBig.smallMorphism.{u, v, max u v} f)
        (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X T) =
      MorphismOfTopoiIn.comp
        (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
        (Big.morphismOfTopoi f))

/- Lemma 61.12.16 (7): `f_small = π_S ∘ f_big ∘ i_T`. -/
@[stacks 098T] #check
  (SmallToBig.smallMorphism_eq_comp_big.{u, v, max u v} f :
    SmallToBig.smallMorphism.{u, v, max u v} f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
          (Big.morphismOfTopoi f))
        (SmallToBig.morphismOfTopoi (𝟙 T)))

/- Lemma 61.12.16 (8): `f_small = π_S ∘ i_f`. -/
@[stacks 098T] #check
  (SmallToBig.smallMorphism_eq_comp.{u, v, max u v} f :
    SmallToBig.smallMorphism.{u, v, max u v} f =
      MorphismOfTopoiIn.comp
        (SmallToBig.siteMorphismOfTopoi.{u, v, max u v} X S)
        (SmallToBig.morphismOfTopoi f))

end AlgebraicGeometry.ChosenBigProetaleSite
