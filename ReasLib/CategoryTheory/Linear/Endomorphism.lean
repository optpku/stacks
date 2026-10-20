/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Endomorphism algebras and fully faithful linear functors

This leaf upgrades the canonical multiplicative equivalence on endomorphisms to an algebra
equivalence whenever the functor is additive and linear.
-/

noncomputable section

universe uR vC uC vD uD

open CategoryTheory

namespace CategoryTheory.Functor.FullyFaithful

variable {R : Type uR} [CommSemiring R]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable {F : C ⥤ D}

/-- A fully faithful additive `R`-linear functor identifies the endomorphism algebras of an
object and its image. -/
@[stacks 09S8 "endomorphism algebra equivalence under a fully faithful linear functor"]
noncomputable def algEquivEnd (hF : F.FullyFaithful)
    [F.Additive] [F.Linear R] (X : C) : End X ≃ₐ[R] End (F.obj X) where
  toEquiv := hF.homEquiv
  map_mul' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The endomorphism-algebra equivalence is induced by the functor's map on morphisms. -/
@[simp, stacks 09S8 "endomorphism algebra equivalence on a morphism"]
theorem algEquivEnd_apply (hF : F.FullyFaithful)
    [F.Additive] [F.Linear R] (X : C) (f : End X) :
    hF.algEquivEnd (R := R) X f = F.map f := sorry

end CategoryTheory.Functor.FullyFaithful
