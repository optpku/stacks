/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

open Scheme.Hom

/-- If the stabilizer fibre at a finite-type point has dimension strictly smaller than
the local source-fibre dimension at the identity, then there is an affine immersed slice
through that point which drops the latter dimension by one and whose slicing source is
Cohen--Macaulay at the restricted identity. -/
theorem existsAffineSliceDimensionDrop
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [CohenMacaulay G.s.left] [LocallyOfFinitePresentation G.s.left]
    [CohenMacaulay G.t.left] [LocallyOfFinitePresentation G.t.left]
    (u : G.U.left) (h_u : IsFiniteTypePoint u) :
    let d₁ := topologicalKrullDim (fiber G.stabilizer.X.hom.left u)
    let d₂ := fiberDimensionAt G.s.left (G.e.left u)
    d₁ < d₂ →
      ∃ U' : Over S, ∃ g : U' ⟶ G.U, ∃ u' : U'.left,
        IsAffine U'.left ∧ IsImmersion g.left ∧ g.left u' = u ∧
          LocallyOfFinitePresentation g.left ∧
          CohenMacaulayAt (sliceSource G g).left
            ((pullbackToTargetSquare G g).left ((G.pullback g).e.left u')) ∧
          fiberDimensionAt (G.pullback g).s.left ((G.pullback g).e.left u') +
            (1 : WithBot ℕ∞) = d₂ := sorry

/-- A Cohen--Macaulay, locally finitely presented groupoid scheme admits an affine
immersed slice through any finite-type point such that the slicing source and both
restricted structure maps retain these properties, and the restricted source-fibre
dimension at the identity equals the dimension of the restricted stabilizer fibre. -/
theorem existsAffineSliceDimensionEqStabilizer
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [CohenMacaulay G.s.left] [LocallyOfFinitePresentation G.s.left]
    [CohenMacaulay G.t.left] [LocallyOfFinitePresentation G.t.left]
    (u : G.U.left) (h_u : IsFiniteTypePoint u) :
    ∃ U' : Over S, ∃ g : U' ⟶ G.U, ∃ u' : U'.left,
      IsAffine U'.left ∧ IsImmersion g.left ∧ g.left u' = u ∧
        LocallyOfFinitePresentation g.left ∧
        CohenMacaulay (sliceSource G g).left ∧
        LocallyOfFinitePresentation (sliceSource G g).left ∧
        CohenMacaulay (G.pullback g).s.left ∧
        LocallyOfFinitePresentation (G.pullback g).s.left ∧
        CohenMacaulay (G.pullback g).t.left ∧
        LocallyOfFinitePresentation (G.pullback g).t.left ∧
        fiberDimensionAt (G.pullback g).s.left ((G.pullback g).e.left u') =
          topologicalKrullDim (fiber (G.pullback g).stabilizer.X.hom.left u') := sorry

end AlgebraicGeometry.GroupoidScheme
