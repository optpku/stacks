/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Products
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product criteria for pseudo-coherence

This file owns the canonical product comparison for derived tensoring by a bounded-above module
complex and the pseudo-coherence criteria detected by that comparison.

@stack 0CYB
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent.ProductCriterion

variable {R : Type u} [CommRing R]

/-- The canonical comparison from tensoring a product of degree-zero modules to the product of
their derived tensor products with `K`. -/
@[stacks 0CYB "canonical derived tensor product comparison"]
noncomputable abbrev comparison
    (K : DerivedCategory (ModuleCat.{u} R)) {A : Type u} (Q : A → ModuleCat.{u} R) :=
  piComparison (DerivedTensor.Bifunctor.leftFunctor K)
    (fun i ↦ ModuleCat.single0Functor.obj (Q i))

/-- A derived-category morphism induces homology isomorphisms above `m` and an epimorphism in
degree `m`. -/
@[stacks 0CYB "homology comparison through a cutoff"]
def IsIsoAboveAndEpiAt
    {X Y : DerivedCategory (ModuleCat.{u} R)} (m : ℤ) (f : X ⟶ Y) : Prop :=
  (∀ i : ℤ, m < i →
    IsIso ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) i).map f)) ∧
    Epi ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) m).map f)

/-- Lemma 15.66.5 (1): for a bounded-above derived `R`-module, pseudo-coherence is equivalent
to invertibility of the canonical derived tensor comparison for arbitrary, constant, or regular
module families. -/
@[stacks 0CYB "pseudo-coherence product criterion"]
theorem pseudoCoherent_tfae (K : D⁻((ModuleCat.{u} R))) :
    List.TFAE [
      K.obj.IsPseudoCoherent,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R), IsIso (comparison K.obj Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        IsIso (comparison K.obj (fun _ : A ↦ Q)),
      ∀ A : Type u,
        IsIso (comparison K.obj (fun _ : A ↦ ModuleCat.of R R))
    ] := sorry
-- Proof strategy: represent `K` by a bounded-above termwise finite-free complex and compare
-- products degreewise; specialize arbitrary families to constant and regular families. For the
-- converse, apply the cutoff criterion for every `m` and use pseudo-coherence iff all cutoffs.

/-- Lemma 15.66.5 (2): `m`-pseudo-coherence of a bounded-above derived `R`-module is equivalent
to the canonical product comparison being a homology isomorphism above `m` and an epimorphism in
degree `m`, for arbitrary, constant, or regular module families. -/
@[stacks 0CYB "m-pseudo-coherence product criterion"]
theorem mPseudoCoherent_tfae (K : D⁻((ModuleCat.{u} R))) (m : ℤ) :
    List.TFAE [
      K.obj.IsMPseudoCoherent m,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        IsIsoAboveAndEpiAt m (comparison K.obj Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        IsIsoAboveAndEpiAt m (comparison K.obj (fun _ : A ↦ Q)),
      ∀ A : Type u,
        IsIsoAboveAndEpiAt m (comparison K.obj (fun _ : A ↦ ModuleCat.of R R))
    ] := sorry
-- Proof strategy: the finite-free approximation gives the cutoff comparison for arbitrary
-- families, and the next two implications are specializations. Conversely, induct on the top
-- nonzero homology degree; the regular-family epimorphism makes that homology finite, and a
-- finite-free cover and its cone lower the bound while preserving the comparison condition.

end CategoryTheory.DerivedCategory.IsPseudoCoherent.ProductCriterion
