/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.ActionFiniteLocallyFree

/-!
# Free finite locally free quotients

A free action of a finite locally free group scheme has representable fppf quotient,
which is an fppf torsor, under the listed alternatives on `X → S` or `G → S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

open AlgebraicGeometry.GroupoidScheme

/- Lemma 66.14.2 (1): the fppf quotient sheaf is a scheme. -/
@[stacks 07S7] #check
  (AlgebraicGeometry.GroupoidScheme.hasRepresentableQuotient_ofAction_fppf :
    ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G),
      [IsFiniteLocallyFree G.X.hom] → [Mod.IsFree X] →
        hasAffineOrbitSourceCondition G X →
          HasRepresentableQuotient StandardTopology.fppf (ofAction G X))

/- Lemma 66.14.2 (2): the quotient morphism is an fppf G-torsor. -/
@[stacks 07S7] #check
  (AlgebraicGeometry.GroupoidScheme.exists_fppfTorsor_ofAction :
    ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G),
      [IsFiniteLocallyFree G.X.hom] → [Mod.IsFree X] →
        hasAffineOrbitSourceCondition G X →
          ∃ (M : Over S) (q : X.X ⟶ M)
            (h_eq : (ofAction G X).toPreRelation.t ≫ q =
              (ofAction G X).toPreRelation.s ≫ q),
            IsFiniteLocallyFree q.left ∧
              IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _
                (ofAction G X).toPreRelation (StandardTopology.fppf.overTopology S)
                (StandardTopology.overTopologySubcanonical StandardTopology.fppf S) q h_eq) ∧
                IsIso ((ofAction G X).toPreRelation.kernelPairLift q h_eq) ∧
                  Sheaf.IsLocallySurjective
                    ((@GrothendieckTopology.uliftYoneda.{u + 1} (Over S) _
                        (StandardTopology.fppf.overTopology S)
                        (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)).map q))
