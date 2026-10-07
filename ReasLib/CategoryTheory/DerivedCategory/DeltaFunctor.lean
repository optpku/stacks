module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Canonical Derived-Category Delta Functor

The localization of cochain complexes in an abelian category into its derived
category has canonical connecting morphisms for short exact sequences.  This
file packages the Mathlib construction as a reusable `DeltaFunctor`.
-/

open CategoryTheory.Pretriangulated
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Lemma 13.12.1: the derived-category localization of cochain complexes,
equipped with the canonical connecting morphisms of short exact sequences. -/
@[stacks 0152, stacks 09L0]
noncomputable def Delta.functor :
    DeltaFunctor (CochainComplex C ℤ) (_root_.DerivedCategory C) where
  toFunctor := _root_.DerivedCategory.Q
  additive := inferInstance
  δ := fun {_} hS ↦ _root_.DerivedCategory.triangleOfSESδ hS
  map_distinguished := fun {_} hS ↦ _root_.DerivedCategory.triangleOfSES_distinguished hS
  δ_naturality := fun {_ _} hS hT f ↦
    ⟨(_root_.DerivedCategory.triangleOfSESδ_naturality hS hT f).symm⟩

/-- The underlying functor of `Delta.functor` is the canonical
derived-category localization functor. -/
@[simp, stacks 0152]
theorem Delta.functor_toFunctor :
    (Delta.functor C).toFunctor = _root_.DerivedCategory.Q := sorry

/-- The connecting morphism of `Delta.functor` is the canonical
boundary morphism of a short exact sequence of cochain complexes. -/
@[simp, stacks 0152]
theorem Delta.functor_δ
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    (Delta.functor C).δ hS =
      _root_.DerivedCategory.triangleOfSESδ hS := sorry

end CategoryTheory.DerivedCategory
