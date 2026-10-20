/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
import StacksCheckRecall

@[expose] public section

/-!
# Definition 29.29.1

The reusable relative-dimension API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension`.
-/

/- Definition 29.29.1 (1): pointwise upper relative dimension. -/
@[stacks 02NJ] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDimensionLEAt :
    {X S : AlgebraicGeometry.Scheme} → (X ⟶ S) → ℕ → X → Prop)
#check
  (AlgebraicGeometry.Scheme.Hom.relativeDimensionLEAt_iff :
    ∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (d : ℕ) (x : X),
      AlgebraicGeometry.Scheme.Hom.RelativeDimensionLEAt f d x ↔
        f.fiberDimensionAt x ≤ (d : WithBot ℕ∞))

/- Definition 29.29.1 (2): locally finite-type global upper relative dimension. -/
@[stacks 02NJ] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE :
    {X S : AlgebraicGeometry.Scheme} → (X ⟶ S) → ℕ → Prop)
#check
  (AlgebraicGeometry.Scheme.Hom.relativeDimensionLE_iff :
    ∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (d : ℕ),
      AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE f d ↔
        AlgebraicGeometry.LocallyOfFiniteType f ∧
          ∀ x : X, AlgebraicGeometry.Scheme.Hom.RelativeDimensionLEAt f d x)

/- Definition 29.29.1 (3): fixed relative dimension of nonempty fibres. -/
@[stacks 02NJ] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDimension :
    {X S : AlgebraicGeometry.Scheme} → (X ⟶ S) → ℕ → Prop)
#check
  (AlgebraicGeometry.Scheme.Hom.relativeDimension_iff :
    ∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (d : ℕ),
      AlgebraicGeometry.Scheme.Hom.RelativeDimension f d ↔
        AlgebraicGeometry.LocallyOfFiniteType f ∧
          (∀ (s : S) (_ : Nonempty (f.fiber s)),
            TopologicalSpace.EquidimensionalSpace (f.fiber s)) ∧
          ∀ (s : S) (_ : Nonempty (f.fiber s)),
            topologicalKrullDim (f.fiber s) = d)
