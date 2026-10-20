/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.Representative
import StacksCheckRecall

/-!
# Scalar extension of two-term representatives

This file is the source-facing recall for Lemma 15.85.6.

@stack 0G9G
-/

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 15.85.6, commutative-ring specialization: extending a two-term representative whose
degree-zero term is flat represents `τ≥-1` of the derived scalar extension. -/
@[stacks 0G9G "Lemma 15.85.6"]
#check fun {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    {K : DerivedCategory (ModuleCat R)} {P : CochainComplex (ModuleCat R) ℤ}
    (hP : IsTwoTermRepresentative K P) (hflat0 : Module.Flat R (P.X 0)) =>
  (IsTwoTermRepresentative.extension_truncGE σ hP hflat0 :
    IsTwoTermRepresentative
      ((t.truncGE (-1)).obj ((ModuleCat.derivedExtensionOfScalars σ).obj K))
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
