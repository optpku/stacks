/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.FieldExtension

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 44.6.5: over a separably closed field, an invertible module on the base change of a
smooth projective curve admits a twist from the original curve with one-dimensional H⁰ and
vanishing H¹. -/
@[stacks 0B9Y] #check
  (AlgebraicGeometry.Scheme.Modules.FieldExtension.exists_twist_with_h0_finrank_one_h1_zero :
    ∀ {k K : Type u} [Field k] [IsSepClosed k] [Field K] [Algebra k K]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [Smooth X.hom] [Projective X.hom]
      [GeometricallyIrreducible X.hom] (g : ℕ)
      (h_genus : AlgebraicGeometry.Curve.genus X = g)
      (L : (AlgebraicGeometry.FieldExtension.baseChange k K X.hom).Modules)
      [Scheme.Modules.Invertible L],
      ∃ (L₀ : X.left.Modules) (_ : Scheme.Modules.Invertible L₀),
        Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.FieldExtension.toBase k K X.hom)
            (L ⊗ AlgebraicGeometry.Scheme.Modules.FieldExtension.baseChange k K X.hom L₀) 0 = 1 ∧
          IsZero (Scheme.Hom.cohomology (AlgebraicGeometry.FieldExtension.toBase k K X.hom)
            (L ⊗ AlgebraicGeometry.Scheme.Modules.FieldExtension.baseChange k K X.hom L₀) 1))
