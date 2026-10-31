/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Slicing.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

open Scheme.Hom

/- Lemma 40.12.3: a Cohen--Macaulay, locally finitely presented groupoid scheme has
an affine immersed slice through any finite-type point such that the slicing source and
both restricted structure maps retain these properties, and the restricted source-fibre
dimension at the identity equals the dimension of the restricted stabilizer fibre. -/
@[stacks 04MZ] #check
  (AlgebraicGeometry.GroupoidScheme.existsAffineSliceDimensionEqStabilizer :
    {S : Scheme.{u}} → (G : GroupoidScheme S) →
    [CohenMacaulay G.s.left] → [LocallyOfFinitePresentation G.s.left] →
    [CohenMacaulay G.t.left] → [LocallyOfFinitePresentation G.t.left] →
    (u : G.U.left) → IsFiniteTypePoint u →
      ∃ U' : Over S, ∃ g : U' ⟶ G.U, ∃ u' : U'.left,
        IsAffine U'.left ∧ IsImmersion g.left ∧ g.left u' = u ∧
          LocallyOfFinitePresentation g.left ∧
          CohenMacaulay (saturationMap G g).left ∧
          LocallyOfFinitePresentation (saturationMap G g).left ∧
          CohenMacaulay (G.pullback g).s.left ∧
          LocallyOfFinitePresentation (G.pullback g).s.left ∧
          CohenMacaulay (G.pullback g).t.left ∧
          LocallyOfFinitePresentation (G.pullback g).t.left ∧
          fiberDimensionAt (G.pullback g).s.left ((G.pullback g).e.left u') =
            topologicalKrullDim (fiber (G.pullback g).stabilizer.X.hom.left u'))

end AlgebraicGeometry.GroupoidScheme
