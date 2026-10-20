/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable
public import ReasLib.AlgebraicGeometry.GroupScheme.Classifying
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Finite type from a smooth cover of a classifying stack
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme

/-- An affine group scheme over a field is of finite type if its classifying
stack of fppf torsors admits a smooth surjective morphism from a scheme. -/
theorem finiteType_of_classifyingStack_smoothCover
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left]
    (hcover :
      ∃ (U : Over (Spec (CommRingCat.of k)))
        (p : Classifying.slice U ⟶ classifyingStack G),
        Classifying.Smooth p ∧ Classifying.Surjective p) :
    Scheme.Hom.FiniteType G.X.hom := sorry

end AlgebraicGeometry.GroupScheme
