/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small

/-!
# Lemma 34.3.13

This file is the source-facing compatibility surface for the reusable
small-to-big Zariski relocalization API.  The neutral owner is
`AlgebraicGeometry.Scheme.Zariski.SmallToBig`; the declarations below retain
the historical chapter names needed by later source files.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- The relocalization functor from `T_{Zar}` to the big Zariski slice over `S`. -/
abbrev smallZariskiToBigZariskiFunctor : T.smallZariskiSite ⥤ S.bigZariskiSite :=
  Zariski.SmallToBig.relocalizationFunctor f

/-- The morphism of topoi induced by small-to-big Zariski relocalization. -/
noncomputable abbrev smallZariskiToBigZariskiMorphismOfTopoi
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    MorphismOfTopoiIn S.bigZariskiTopology T.smallZariskiTopology :=
  Zariski.SmallToBig.morphismOfTopoi f

/- Lemma 34.3.13 (1): the relocalization functor is cocontinuous. -/
@[stacks 020Y] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor_isCocontinuous f :
    Functor.IsCocontinuous
      (AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor f)
      T.smallZariskiTopology S.bigZariskiTopology)

/- Lemma 34.3.13 (2): the relocalization induces a morphism of topoi. -/
@[stacks 020Y] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.morphismOfTopoi f :
    MorphismOfTopoiIn S.bigZariskiTopology T.smallZariskiTopology)

/- Lemma 34.3.13 (3): inverse image is computed on the same scheme over `S`. -/
@[stacks 020Y] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.inverseImage_obj_obj f :
    ∀ (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : T.smallZariskiSite),
      ((AlgebraicGeometry.Scheme.Zariski.SmallToBig.inverseImage f).obj 𝒢).1.obj (op U) =
        𝒢.1.obj (op ((AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor f).obj U)))

/- Lemma 34.3.13 (4): lower shriek is left adjoint to inverse image. -/
@[stacks 020Y] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.lowerShriekAdjunction f :
    AlgebraicGeometry.Scheme.Zariski.SmallToBig.lowerShriek f ⊣
      AlgebraicGeometry.Scheme.Zariski.SmallToBig.inverseImage f)

/- Lemma 34.3.13 (5): lower shriek preserves fibre products. -/
@[stacks 020Y] #check
  (CategoryTheory.Functor.SheafPullback.Pullbacks.preservesPullbacks.{u + 1, u, u, u + 1, u + 1}
    (AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor f) :
      PreservesLimitsOfShape WalkingCospan
        (AlgebraicGeometry.Scheme.Zariski.SmallToBig.lowerShriek.{u, u + 1} f))

/- Lemma 34.3.13 (6): lower shriek preserves equalizers. -/
@[stacks 020Y] #check
  (CategoryTheory.Functor.SheafPullback.Pullbacks.preservesEqualizers.{u + 1, u, u, u + 1, u + 1}
    (AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor f) :
      PreservesLimitsOfShape WalkingParallelPair
        (AlgebraicGeometry.Scheme.Zariski.SmallToBig.lowerShriek.{u, u + 1} f))

end AlgebraicGeometry.Scheme
