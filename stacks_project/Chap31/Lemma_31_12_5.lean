/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Stalk

open CategoryTheory
open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 31.12.5: for an integral locally Noetherian scheme and a coherent module sheaf,
reflexivity is equivalent to reflexivity of every stalk and to reflexivity of every closed-point
stalk. -/
@[stacks 0AY3] #check
  (AlgebraicGeometry.Scheme.Modules.isReflexive_tfae_stalk_and_closedPointStalk :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      List.TFAE
        [ AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ
        , ∀ x : X,
            Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)
        , ∀ x : X, x ∈ closedPoints X →
            Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)
        ])
