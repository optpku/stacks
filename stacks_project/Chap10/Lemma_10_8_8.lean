/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCheckRecall

/-!
# Homology and directed colimits of modules

@stack 00DB
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ShortComplex

universe u v

noncomputable section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {L M N : I ⥤ ModuleCat R}
variable {φ : L ⟶ M} {ψ : M ⟶ N}

/-- The pointwise complex condition assembles to the zero composite of natural transformations. -/
theorem module_system_comp_eq_zero
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    φ ≫ ψ = 0 := sorry

/-- The short complex in the functor category attached to a pointwise complex
`L -> M -> N`. -/
noncomputable def module_system_shortComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    ShortComplex (I ⥤ ModuleCat R) :=
  .mk φ ψ (module_system_comp_eq_zero hcomp)

/-- Lemma 10.8.8 (00DB), clause (1): the stagewise homology modules form a system over `I`. -/
@[stacks 00DB "(1), stagewise homology system"]
noncomputable def module_system_homology
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    I ⥤ ModuleCat R :=
  (ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp) ⋙
    homologyFunctor (ModuleCat R)

/-- Lemma 10.8.8 (00DB), clause (2): taking colimits preserves the complex condition. -/
@[stacks 00DB "(2), colimit complex"]
theorem colimit_module_system_isComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    colim.map φ ≫ colim.map ψ = 0 := sorry

/-- The canonical comparison from the colimit of stagewise homology to the homology of the
colimit short complex. -/
noncomputable def module_system_homology_comparison
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :=
  colimit.post
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp))
    (homologyFunctor (ModuleCat R))

variable [IsDirectedOrder I]

/-- Lemma 10.8.8 (00DB), clause (3): the homology comparison for a directed system is an
isomorphism. -/
@[stacks 00DB "(3), homology commutes with the directed colimit"]
theorem module_system_homology_comparison_isIso
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := sorry

noncomputable instance (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) :=
  module_system_homology_comparison_isIso hcomp

@[stacks 00DB "short-complex diagrams in a functor category"]
#check @ShortComplex.functorEquivalence

@[stacks 00DB "homology functor"]
#check @ShortComplex.homologyFunctor

@[stacks 00DB "canonical colimit comparison"]
#check @CategoryTheory.Limits.colimit.post
