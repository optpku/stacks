module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A flat proper finitely presented morphism with geometrically connected and reduced fibres over
a connected base induces an exact sequence of étale fundamental groups, surjective onto the base
group. The geometric fibre is based at `xbar`, the total space at
`xbar ≫ pullback.fst f sbar`, and the base at its image under `f`. The condition
`hpoint` and the pullback identity identify this last point with `sbar`. -/
theorem homotopyExactSequence
    (f : X ⟶ S) [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (sbar : Spec (.of Ω) ⟶ S) (xbar : Spec (.of Ω) ⟶ pullback f sbar)
    (hpoint : xbar ≫ pullback.snd f sbar = 𝟙 (Spec (.of Ω))) :
    Function.MulExact (fundamentalGroupMap (pullback.fst f sbar) xbar)
      (fundamentalGroupMap f (xbar ≫ pullback.fst f sbar)) ∧
    Function.Surjective (fundamentalGroupMap f (xbar ≫ pullback.fst f sbar)) := sorry

end AlgebraicGeometry.Scheme.Hom
