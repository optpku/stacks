/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Henselization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.35.5: a henselization of the stalk at a point is isomorphic to the filtered
colimit of the global-section rings of the elementary étale neighborhoods of that point. -/
@[stacks 05KS] #check
  (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.nonempty_henselizationIsoColimit :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (s : S) (Rh : Type u),
      [CommRing Rh] → [Algebra (S.presheaf.stalk s) Rh] →
      [IsHenselizationOf (S.presheaf.stalk s) Rh] →
      Nonempty
        ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of Rh) ≅
          colimit
            (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.sections S s)))
