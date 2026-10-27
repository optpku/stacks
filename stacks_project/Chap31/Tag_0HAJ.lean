/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Rank.Generic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory.MonoidalCategory

/- Lemma (0HAJ) (1): On an integral scheme, generic cardinal rank is
multiplicative for tensor products of quasi-coherent modules. -/
@[stacks 0HAJ] #check (AlgebraicGeometry.Scheme.Modules.genericRank_tensor :
  ∀ {X : Scheme} [IsIntegral X] (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
    genericRank (F ⊗ G) = genericRank F * genericRank G)

/- Lemma (0HAJ) (2): On an integral scheme, generic cardinal rank is
multiplicative for internal sheaf Hom when the source is finitely presented
and the target is quasi-coherent. Finite presentation already implies
quasi-coherence of the source. -/
@[stacks 0HAJ] #check (AlgebraicGeometry.Scheme.Modules.genericRank_internalHom :
  ∀ {X : Scheme} [IsIntegral X] (F G : X.Modules) [F.IsFinitePresentation]
    [G.IsQuasicoherent], genericRank (internalHom F G) = genericRank F * genericRank G)
