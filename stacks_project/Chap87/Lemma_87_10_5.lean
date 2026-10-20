/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Noetherian
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u

/- Lemma 87.10.5. Let S be a scheme and X an affine formal algebraic space.
The following are equivalent: X is Noetherian; X is adic* and every scheme
closed-immersed into X is Noetherian; X is adic* and admits a directed affine
thickening presentation as in Definition 87.9.1 with Noetherian stages; X is
weakly adic and admits such a presentation with Noetherian stages. -/
@[stacks 0AKM] #check (AlgebraicGeometry.IsNoetherianAffine.tfae :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    (X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))
    [IsAffineFormalAlgebraicSpace X],
    List.TFAE [IsNoetherianAffine X,
      IsAdicStar X ∧ IsNoetherianAffine.forallClosedImmersionIsNoetherian X,
      IsAdicStar X ∧ IsNoetherianAffine.existsNoetherianThickeningColimit X,
      IsWeaklyAdicAffine X ∧ IsNoetherianAffine.existsNoetherianThickeningColimit X])
