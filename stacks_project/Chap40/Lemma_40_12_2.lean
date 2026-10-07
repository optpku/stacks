module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Slicing.Dimension

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

open Scheme.Hom

/- Lemma 40.12.2: if the stabilizer fibre at a finite-type point has dimension strictly
smaller than the local source-fibre dimension at the identity, then an affine immersion
through that point cuts the latter dimension by one while preserving Cohen--Macaulayness
at the restricted identity. -/
@[stacks 0461] #check
  (AlgebraicGeometry.GroupoidScheme.existsAffineSliceDimensionDrop :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [CohenMacaulay G.s.left] [LocallyOfFinitePresentation G.s.left]
      [CohenMacaulay G.t.left] [LocallyOfFinitePresentation G.t.left]
      (u : G.U.left) (_ : IsFiniteTypePoint u),
      let d₁ := topologicalKrullDim (fiber G.stabilizer.X.hom.left u)
      let d₂ := fiberDimensionAt G.s.left (G.e.left u)
      d₁ < d₂ →
        ∃ U' : Over S, ∃ g : U' ⟶ G.U, ∃ u' : U'.left,
          IsAffine U'.left ∧ IsImmersion g.left ∧ g.left u' = u ∧
            LocallyOfFinitePresentation g.left ∧
            CohenMacaulayAt (sliceSource G g).left
              ((pullbackToTargetSquare G g).left ((G.pullback g).e.left u')) ∧
            fiberDimensionAt (G.pullback g).s.left ((G.pullback g).e.left u') +
              (1 : WithBot ℕ∞) = d₂)

end AlgebraicGeometry.GroupoidScheme
