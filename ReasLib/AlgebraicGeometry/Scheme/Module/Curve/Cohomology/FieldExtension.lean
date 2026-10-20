/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

/-!
# Cohomology of curve modules after field extension

This file records the existence of a twist with one-dimensional global sections and vanishing
first cohomology for an invertible module after extending the base field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.FieldExtension

/-- For a separably closed field and a smooth projective geometrically irreducible curve, an
invertible module after a field extension admits an invertible twist from the original curve whose
global sections have dimension one and whose first cohomology vanishes. -/
theorem exists_twist_with_h0_finrank_one_h1_zero
    {k K : Type u} [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] (g : ℕ) (h_genus : AlgebraicGeometry.Curve.genus X = g)
    (L : (AlgebraicGeometry.FieldExtension.baseChange k K X.hom).Modules)
    [Scheme.Modules.Invertible L] :
    ∃ (L₀ : X.left.Modules) (_ : Scheme.Modules.Invertible L₀),
      Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.FieldExtension.toBase k K X.hom)
          (L ⊗ baseChange k K X.hom L₀) 0 = 1 ∧
        IsZero (Scheme.Hom.cohomology (AlgebraicGeometry.FieldExtension.toBase k K X.hom)
          (L ⊗ baseChange k K X.hom L₀) 1) := sorry

end AlgebraicGeometry.Scheme.Modules.FieldExtension
