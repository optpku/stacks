/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.29.3

The concrete algebraic DG owner packages derived tensor, derived fixed-source internal Hom, and
their adjunction.  `Adjunction.derived` remains the construction-neutral engine.  A ringed-site
specialization will be a thin application once its tensor and internal-Hom functors are shared.
-/

@[stacks 0FTQ] #check @DifferentialGradedBimodule.TensorHom.derivedAdjunction
#check @DifferentialGradedBimodule.TensorHom.derivedHomEquiv
#check @CategoryTheory.Adjunction.derived
#check @CategoryTheory.Functor.LeftDerived.Homotopy.functor
#check @CategoryTheory.Functor.RightDerived.Cochain.functor
#check @CategoryTheory.Functor.LeftDerived.Homotopy.isLeftDerived
#check @CategoryTheory.Functor.RightDerived.Cochain.isRightDerived
