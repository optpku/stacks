/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Density
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Projective
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Remark 30.18.2 (1): the morphism of a Chow modification is H-projective. -/
@[stacks 0201] #check
  (AlgebraicGeometry.ChowLemmaModification.hProjective :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} (M : AlgebraicGeometry.ChowLemmaModification f),
      AlgebraicGeometry.HProjective M.π)

/- Remark 30.18.2 (2): a Chow modification can be chosen so that the preimage of its
distinguished open is scheme-theoretically dense. -/
@[stacks 0201] #check
  (AlgebraicGeometry.ChowLemmaModification.exists_schemeTheoreticallyDense_preimage :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsNoetherian S]
      [AlgebraicGeometry.IsSeparated f] [Scheme.Hom.FiniteType f],
      ∃ M : AlgebraicGeometry.ChowLemmaModification f,
        AlgebraicGeometry.schemeTheoreticallyDense (M.π ⁻¹ᵁ M.denseOpen))

/- Remark 30.18.2 (3): when the original scheme is reduced, the modification can also be chosen
with reduced source while retaining the dense-preimage property. -/
@[stacks 0201] #check
  (AlgebraicGeometry.ChowLemmaModification.exists_schemeTheoreticallyDense_preimage_isReduced :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsNoetherian S]
      [AlgebraicGeometry.IsSeparated f] [Scheme.Hom.FiniteType f]
      [AlgebraicGeometry.IsReduced X],
      ∃ M : AlgebraicGeometry.ChowLemmaModification f,
        AlgebraicGeometry.schemeTheoreticallyDense (M.π ⁻¹ᵁ M.denseOpen) ∧
          AlgebraicGeometry.IsReduced M.X')
