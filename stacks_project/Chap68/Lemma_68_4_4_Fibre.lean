module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove

/-!
# Fibres of a self-pullback over a point of an algebraic space

The fibre of `|U ×_X U| → |X|` over a point is the preimage of that point under
the composite of a self-pullback projection with the chart morphism. This module
records that fibre, its finiteness, and the equivalent existence of a
monomorphism from the spectrum of a field in the point class whose represented
fibre is a finite nonempty scheme over the field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.selfPullbackFibreFiniteOver_iff_isPullback :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} {U : Over S}
    (φ : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ X)
    {R : AlgebraicGeometry.AlgebraicSpace S}
    (fst snd : R ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver U)
    (h : IsPullback fst snd φ φ) (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.selfPullbackFibreFiniteOver φ x ↔
      (AlgebraicGeometry.AlgebraicSpace.Points.map (fst ≫ φ) ⁻¹' {x}).Finite)
