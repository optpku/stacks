/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
import StacksCheckRecall

/-!
# Lemma 34.4.17

The small and big etale morphism API is owned by
`ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback` and
`ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig`.

@stack 021I
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

/- Lemma 34.4.17 (1): small étale base change sends an object over `S` to its
pullback over `T`. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback f : S.Etale ⥤ T.Etale)

/- Lemma 34.4.17 (2): small étale base change is continuous. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isContinuous f :
    Functor.IsContinuous (AlgebraicGeometry.Scheme.smallEtalePullback f)
      S.smallEtaleTopology T.smallEtaleTopology)

/- Lemma 34.4.17 (3): small étale base change defines a morphism of sites. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isMorphismOfSites f :
    CategoryTheory.IsMorphismOfSites S.smallEtaleTopology T.smallEtaleTopology
      (AlgebraicGeometry.Scheme.smallEtalePullback f))

variable [HasSheafify T.smallEtaleTopology (Type (u + 1))]

/- Lemma 34.4.17 (4): small étale base change induces the morphism of topoi
`f_small`. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f :
    MorphismOfTopoiIn S.smallEtaleTopology T.smallEtaleTopology)

/- Lemma 34.4.17 (5): the direct image along `f_small` evaluates a sheaf on
the base-changed object. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_pushforward_obj_obj f :
    ∀ (F : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : S.Etale),
      ((AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f).pushforward.obj F).1.obj
          (op U) =
        F.1.obj (op ((AlgebraicGeometry.Scheme.smallEtalePullback f).obj U)))

/- Lemma 34.4.17 (6): the relocalization morphism factors through the big
étale morphism and the identity-base relocalization. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphism_eq_comp_big f :
    AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f)
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi (𝟙 T)))

/- Lemma 34.4.17 (7): the square comparing the small and big étale
morphisms commutes. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_comp_site f :
    MorphismOfTopoiIn.comp
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f)
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi T) =
      MorphismOfTopoiIn.comp
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)
        (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f))

/- Lemma 34.4.17 (8): `f_small` factors through the big étale morphism and
the identity-base relocalization. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_eq_comp_big f :
    AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)
          (AlgebraicGeometry.Scheme.Etale.Big.morphismOfTopoi f))
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi (𝟙 T)))

/- Lemma 34.4.17 (9): `f_small` is the composite of the small-to-big site
morphism with the relocalization morphism. -/
@[stacks 021I] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_eq_comp f :
    AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f =
      MorphismOfTopoiIn.comp
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi f))

end AlgebraicGeometry.Scheme
