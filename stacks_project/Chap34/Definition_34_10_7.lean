/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
import StacksCheckRecall

@[expose] public section

universe u v

/-!
# Definition 34.10.7

This chapter entry is a compatibility facade for the `V`-covering predicate.
-/

/- Definition 34.10.7: A family of scheme morphisms into `T` is a V covering if,
for every affine open `U` of `T`, there is a finite standard V covering of `U`
refining the family obtained by base change to `U`. -/
@[stacks 0ETH] #check (@AlgebraicGeometry.IsVCovering :
  ∀ (ι : Type v) (T : AlgebraicGeometry.Scheme.{u}) (family : ι → AlgebraicGeometry.Scheme.{u})
    (map : ∀ i, family i ⟶ T), Prop)
#check AlgebraicGeometry.IsVCovering.exists_affineOpen_refinement
#check AlgebraicGeometry.Scheme.VCovering
