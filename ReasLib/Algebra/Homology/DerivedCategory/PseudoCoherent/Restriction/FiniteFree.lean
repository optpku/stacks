/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free models after restriction of scalars

This file provides bounded-above finite-free models for derived modules that become
pseudo-coherent after restricting scalars along a finite-free algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {A B : Type u} [CommRing A] [Ring B] [Algebra A B]
variable [Module.Free A B] [Module.Finite A B]

/-- A derived module that is pseudo-coherent after restriction along a finite-free algebra
admits a bounded-above termwise finite-free model over that algebra. -/
@[stacks 0CSF "finite-free restriction model"]
theorem exists_finiteFree_model_of_restrictScalars_of_finiteFree
    (K : DerivedCategory (ModuleCat B))
    (hK : ((ModuleCat.restrictScalars
      (algebraMap A B)).mapDerivedCategory.obj K).IsPseudoCoherent) :
    ∃ (P : CochainComplex (ModuleCat B) ℤ) (_ : DerivedCategory.Q.obj P ≅ K),
      CochainComplex.minus (ModuleCat B) P ∧ P.IsTermwiseFiniteFree := sorry

end CategoryTheory.DerivedCategory.IsPseudoCoherent
