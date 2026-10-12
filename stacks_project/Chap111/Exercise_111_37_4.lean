/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Examples.SpecialFiber.Coproduct
public import ReasLib.AlgebraicGeometry.Examples.SpecialFiber.Properties
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

/- Exercise 111.37.4 (1): the scheme-theoretic fibre of `SplitConicOverLine.toBase` over every
closed point of `Spec (Polynomial ℂ)` other than the origin is isomorphic to `ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.SplitConicOverLine.fiber_iso_projectiveLine :
  (t : AlgebraicGeometry.SplitConicOverLine.base) →
    t ∈ closedPoints AlgebraicGeometry.SplitConicOverLine.base →
      t ≠ AlgebraicGeometry.SplitConicOverLine.origin →
        Nonempty (AlgebraicGeometry.SplitConicOverLine.toBase.fiber t ≅
          AlgebraicGeometry.ProjectiveLine.scheme ℂ))

/- Exercise 111.37.4 (2): the special fibre of `SplitConicOverLine.toBase` is not isomorphic to
`ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.SplitConicOverLine.specialFiber_not_iso_projectiveLine :
  ¬ Nonempty (AlgebraicGeometry.SplitConicOverLine.specialFiber ≅
    AlgebraicGeometry.ProjectiveLine.scheme ℂ))

/- Exercise 111.37.4 (3): the special fibre of `SplitConicOverLine.toBase` is projective over the
residue field of the origin. -/
@[stacks 02A0] #check (AlgebraicGeometry.SplitConicOverLine.specialFiber_projective :
  Projective (AlgebraicGeometry.SplitConicOverLine.toBase.fiberToSpecResidueField
    AlgebraicGeometry.SplitConicOverLine.origin))

/- Exercise 111.37.4 (4a): the scheme-theoretic fibre of `DoubleLineOverLine.toBase` over every
closed point other than the origin is isomorphic to `ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.DoubleLineOverLine.fiber_iso_projectiveLine :
  (t : AlgebraicGeometry.DoubleLineOverLine.base) →
    t ∈ closedPoints AlgebraicGeometry.DoubleLineOverLine.base →
      t ≠ AlgebraicGeometry.DoubleLineOverLine.origin →
        Nonempty (AlgebraicGeometry.DoubleLineOverLine.toBase.fiber t ≅
          AlgebraicGeometry.ProjectiveLine.scheme ℂ))

/- Exercise 111.37.4 (4b): the special fibre of `DoubleLineOverLine.toBase` is not isomorphic to
`ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.DoubleLineOverLine.specialFiber_not_iso_projectiveLine :
  ¬ Nonempty (AlgebraicGeometry.DoubleLineOverLine.specialFiber ≅
    AlgebraicGeometry.ProjectiveLine.scheme ℂ))

/- Exercise 111.37.4 (4): the special fibre of `DoubleLineOverLine.toBase` is irreducible and
projective. -/
@[stacks 02A0] #check (AlgebraicGeometry.DoubleLineOverLine.specialFiber_irreducible_projective :
  IrreducibleSpace AlgebraicGeometry.DoubleLineOverLine.specialFiber ∧
    Projective (AlgebraicGeometry.DoubleLineOverLine.toBase.fiberToSpecResidueField
      AlgebraicGeometry.DoubleLineOverLine.origin))

/- Exercise 111.37.4 (5): the special fibre of `NonflatProjectiveFiber.hom` is integral and
projective. -/
@[stacks 02A0] #check (AlgebraicGeometry.NonflatProjectiveFiber.specialFiber_integral_projective :
  IsIntegral AlgebraicGeometry.NonflatProjectiveFiber.specialFiber ∧
    Projective (AlgebraicGeometry.NonflatProjectiveFiber.hom.fiberToSpecResidueField
      AlgebraicGeometry.NonflatProjectiveFiber.origin))

/- Exercise 111.37.4 (5a): the scheme-theoretic fibre of `NonflatProjectiveFiber.hom` over every
closed point other than the origin is isomorphic to `ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.NonflatProjectiveFiber.fiber_iso_projectiveLine :
  (t : AlgebraicGeometry.NonflatProjectiveFiber.base) →
    t ∈ closedPoints AlgebraicGeometry.NonflatProjectiveFiber.base →
      t ≠ AlgebraicGeometry.NonflatProjectiveFiber.origin →
        Nonempty (AlgebraicGeometry.NonflatProjectiveFiber.hom.fiber t ≅
          AlgebraicGeometry.ProjectiveLine.scheme ℂ))

/- Exercise 111.37.4 (5b): the special fibre of `NonflatProjectiveFiber.hom` is not isomorphic to
`ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.NonflatProjectiveFiber.specialFiber_not_iso_projectiveLine :
  ¬ Nonempty (AlgebraicGeometry.NonflatProjectiveFiber.specialFiber ≅
    AlgebraicGeometry.ProjectiveLine.scheme ℂ))

/- Exercise 111.37.4 (6): the special fibre of `NonflatProjectiveFiber.hom` is smooth and
projective. -/
@[stacks 02A0] #check (AlgebraicGeometry.NonflatProjectiveFiber.specialFiber_smooth_projective :
  Smooth (AlgebraicGeometry.NonflatProjectiveFiber.hom.fiberToSpecResidueField
    AlgebraicGeometry.NonflatProjectiveFiber.origin) ∧
    Projective (AlgebraicGeometry.NonflatProjectiveFiber.hom.fiberToSpecResidueField
      AlgebraicGeometry.NonflatProjectiveFiber.origin))

/- Exercise 111.37.4 (7): the split-conic morphism `SplitConicOverLine.toBase` is flat. -/
@[stacks 02A0] #check (AlgebraicGeometry.SplitConicOverLine.toBase_flat :
  Flat AlgebraicGeometry.SplitConicOverLine.toBase)

/- Exercise 111.37.4 (8): `SplitConicOverLine.toBase` is a flat projective morphism. -/
@[stacks 02A0] #check (AlgebraicGeometry.SplitConicOverLine.toBase_projective :
  Projective AlgebraicGeometry.SplitConicOverLine.toBase)

/- Exercise 111.37.4 (9): `SplitConicOverLine.toBase` is flat and projective with reduced special fibre. -/
@[stacks 02A0] #check (AlgebraicGeometry.SplitConicOverLine.specialFiber_reduced :
  IsReduced AlgebraicGeometry.SplitConicOverLine.specialFiber)

/- Exercise 111.37.4 (10): `DoubleLineOverLine.toBase` is flat and projective with irreducible
special fibre. -/
@[stacks 02A0] #check (AlgebraicGeometry.DoubleLineOverLine.flat_projective_irreducible_specialFiber :
  Flat AlgebraicGeometry.DoubleLineOverLine.toBase ∧
    Projective AlgebraicGeometry.DoubleLineOverLine.toBase ∧
      IrreducibleSpace AlgebraicGeometry.DoubleLineOverLine.specialFiber)

/- Exercise 111.37.4 (11): there is no flat projective morphism to `Spec (Polynomial ℂ)` whose
closed fibres away from the origin are isomorphic to `ProjectiveLine.scheme ℂ` and whose special
fibre is integral but not isomorphic to `ProjectiveLine.scheme ℂ`. -/
@[stacks 02A0] #check (AlgebraicGeometry.SpecialFiberDegeneration.noFlatProjectiveIntegralDegeneration :
  ¬ ∃ (X : Scheme) (f : X ⟶ AlgebraicGeometry.SplitConicOverLine.base),
      Flat f ∧ Projective f ∧
        (∀ t : AlgebraicGeometry.SplitConicOverLine.base,
          t ∈ closedPoints AlgebraicGeometry.SplitConicOverLine.base →
            t ≠ AlgebraicGeometry.SplitConicOverLine.origin →
              Nonempty (f.fiber t ≅ AlgebraicGeometry.ProjectiveLine.scheme ℂ)) ∧
        ¬ Nonempty (f.fiber AlgebraicGeometry.SplitConicOverLine.origin ≅
          AlgebraicGeometry.ProjectiveLine.scheme ℂ) ∧
        IsIntegral (f.fiber AlgebraicGeometry.SplitConicOverLine.origin))
