/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free subcomplexes

This leaf owns the existence of a bounded finite-free subcomplex containing a prescribed finite
family of homogeneous elements.

@stack 0FNR
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex

variable {R : Type u} [Ring R]
variable {ι : Type*} [Finite ι]

/-- Lemma 15.127.2: a bounded-above complex of free modules contains any prescribed finite
family of homogeneous elements in a bounded finite-free subcomplex. -/
@[stacks 0FNR "bounded finite-free subcomplex containing a finite family"]
theorem exists_boundedFiniteFree_subobject_containing
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ b : ℤ, F.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free R (F.X n))
    (degrees : ι → ℤ) (elements : ∀ i : ι, F.X (degrees i)) :
    ∃ G : Subobject F,
      (∃ a b : ℤ,
          ((G : CochainComplex (ModuleCat.{u} R) ℤ).IsStrictlyGE a) ∧
            ((G : CochainComplex (ModuleCat.{u} R) ℤ).IsStrictlyLE b)) ∧
      ((G : CochainComplex (ModuleCat.{u} R) ℤ).IsTermwiseFiniteFree) ∧
      ∀ i : ι,
        ∃ g : (G : CochainComplex (ModuleCat.{u} R) ℤ).X (degrees i),
          G.arrow.f (degrees i) g = elements i := sorry
-- Proof strategy: choose the upper support bound from `hbounded`, then recurse down through the
-- finitely many relevant degrees.  In each free term, enlarge the finite set of prescribed
-- elements and incoming differential images to a finite free direct summand, and package the
-- compatible inclusions as a bounded `Subobject F` with the required lifts.

end CochainComplex
