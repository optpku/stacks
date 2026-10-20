/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace.Immersion
import StacksCheckRecall

/-!
# Embedding an affine scheme into affine space over an algebraic space

A locally finite type morphism from an affine scheme into a quasi-separated,
locally separated algebraic space immerses into a finite-dimensional relative
affine space over the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry


universe u
/- Lemma 70.13.1: Let `S` be a scheme. Let `f : U ⟶ X` be a morphism of
algebraic spaces over `S`. Assume `U` is an affine scheme, `f` is locally of
finite type, and `X` is quasi-separated and locally separated in the absolute
sense. Then there exists an immersion `U ⟶ AffineSpace (ULift (Fin n)) X` over
`X`. -/
@[stacks 088L] #check (AlgebraicGeometry.AlgebraicSpace.exists_immersion_to_affineSpace :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X)
      [IsAffine U] [LocallyOfFiniteType f]
      [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyLocallySeparated X],
      AlgebraicGeometry.AlgebraicSpace.existsImmersionToAffineSpace f)
