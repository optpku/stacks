/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Colimits
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.42.6

The source specializations are direct consequences of the finite connected
colimit API for almost cocontinuous pushforward.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [K.WEqualsLocallyBijective (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/- Lemma 7.42.6 (08LS) (1): the direct image associated to a continuous almost
cocontinuous functor commutes with pushouts. -/
@[stacks 04BA "(1)"] #check
  (PreservesFiniteConnectedColimits.preservesColimitsOfShape
      (u.sheafPushforwardContinuous (Type w) J K) WalkingSpan :
    PreservesColimitsOfShape WalkingSpan
      (u.sheafPushforwardContinuous (Type w) J K))

/- Lemma 7.42.6 (08LS) (2): the same direct image commutes with coequalizers. -/
@[stacks 04BA "(2)"] #check
  (PreservesFiniteConnectedColimits.preservesColimitsOfShape
      (u.sheafPushforwardContinuous (Type w) J K) WalkingParallelPair :
    PreservesColimitsOfShape WalkingParallelPair
      (u.sheafPushforwardContinuous (Type w) J K))
