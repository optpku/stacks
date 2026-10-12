/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Étale maps after filtered-colimit base change

This categorical leaf owns the arbitrary filtered-diagram form of étale
descent; preorder-indexed direct-limit specializations live in sibling leaves.

@stack 07RI
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u v

namespace CommAlgCat.FilteredColimit.Etale

variable {A : Type u} [CommRing A]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
variable {B C : Type u} [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- Stacks tag `07RI`: étaleness of the base change of a finitely presented
algebra map to a filtered colimit is witnessed at one diagram object. -/
@[stacks 07RI "etale filtered-colimit descent"]
theorem exists_stage
    (φ : B →ₐ[A] C) (hfinitePresentation : φ.FinitePresentation)
    (hetale : (Algebra.TensorProduct.map φ (AlgHom.id A (colimit F : CommAlgCat.{u} A))).Etale) :
    ∃ j : J, (Algebra.TensorProduct.map φ (AlgHom.id A (F.obj j))).Etale := sorry

end CommAlgCat.FilteredColimit.Etale
