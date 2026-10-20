/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-independent derived base change

This leaf records when the explicit derived comparison around a tensor-product pushout square is
an isomorphism.

@stack 0661
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- Lemma 15.61.2: the derived tensor-product pushout comparison is an isomorphism when the two
algebras are Tor independent over the base ring. -/
@[stacks 0661 "Tor-independent derived base-change comparison"]
theorem comparisonApp_isIso_of_torIndependent
    (K : DerivedCategory (ModuleCat A))
    (h : ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    IsIso (comparisonApp (R := R) (A := A) (R' := R') K) := sorry

end CategoryTheory.ModuleCat.Pushout.DerivedExtension.TensorProduct
