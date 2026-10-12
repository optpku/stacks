/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree
import StacksCheckRecall

@[expose] public section

/-!
# Definition 29.57.1

The reusable fibre-degree and boundedness API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree`.
-/

/- Definition 29.57.1 (1): a numerical degree bound includes finiteness of every residue-field
fibre. -/
@[stacks 03J4] #check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_iff :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (n : ℕ),
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n ↔
        ∀ y : Y, AlgebraicGeometry.IsFinite (f.fiberToSpecResidueField y) ∧
          AlgebraicGeometry.Scheme.Hom.fiberDegree f y ≤ n)

/- Definition 29.57.1 (2): universal boundedness is the existence of one such degree bound. -/
@[stacks 03J4] #check
  (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_iff :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f ↔
        ∃ n : ℕ, AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n)
