/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper birational morphism between integral Noetherian regular schemes of dimension
two is the composite of an endpoint isomorphism and a finite sequence of closed-point blowups. -/
theorem exists_pointBlowupSequence {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [Scheme.Regular X] [Scheme.Regular Y] (f : X ⟶ Y)
    [IsProper f] [IsBirational f] (hX_dim : topologicalKrullDim X = 2)
    (hY_dim : topologicalKrullDim Y = 2) :
    ∃ (Xn : Scheme.{u}) (s : Scheme.PointBlowupSequence Y Xn) (e : X ≅ Xn),
      e.hom ≫ s.toSource = f := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- Proper integral regular surfaces over a Noetherian scheme are birational over the base
exactly when they admit finite closed-point blowup sequences to a common terminal scheme
whose composites to the base agree. -/
theorem birationalOver_iff_exists_commonPointBlowups
    {S X Y : Scheme.{u}} [IsNoetherian S] [X.Over S] [Y.Over S]
    [IsIntegral X] [IsIntegral Y] [Scheme.Regular X] [Scheme.Regular Y]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (hX_dim : topologicalKrullDim X = 2) (hY_dim : topologicalKrullDim Y = 2) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      ∃ (Z : Scheme.{u}) (sX : PointBlowupSequence X Z) (sY : PointBlowupSequence Y Z),
        sX.toSource ≫ (X ↘ S) = sY.toSource ≫ (Y ↘ S) := sorry

end AlgebraicGeometry.Scheme
