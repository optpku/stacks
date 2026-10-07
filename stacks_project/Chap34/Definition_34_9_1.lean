module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

@[expose] public section

/-!
# Definition 34.9.1

This chapter entry is a compatibility facade for canonical fpqc covering
families and their finite affine-refinement characterization.
-/

universe u v

/- Definition 34.9.1: An fpqc covering of a scheme `T` is an indexed family
of morphisms to `T` whose members are flat and which admits a finite affine
refinement over every affine open of `T`. -/
@[stacks 022B] #check (AlgebraicGeometry.Scheme.FpqcCovering :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (ι → CategoryTheory.Over T) → Prop)

#check (AlgebraicGeometry.fpqcCovering_iff_flat_and_hasAffineRefinement :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (family : ι → CategoryTheory.Over T) →
      AlgebraicGeometry.Scheme.FpqcCovering family ↔
        (∀ i : ι, AlgebraicGeometry.Flat (family i).hom) ∧
          AlgebraicGeometry.HasAffineRefinement family)
