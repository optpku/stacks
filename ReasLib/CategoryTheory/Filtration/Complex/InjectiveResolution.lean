/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteDiagram
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Strict filtered-injective resolutions of bounded-below complexes

Bounded-below complexes of finite decreasing filtration diagrams have replacements
whose terms have injective graded pieces and whose comparison maps are termwise
strict monomorphisms and quasi-isomorphisms on every associated graded complex.
-/

@[expose] public section

universe v u

namespace CategoryTheory.FiniteFilteredDiagram

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- A complex of finite filtration diagrams vanishing below an integer admits a
replacement vanishing below the same integer, with filtered-injective terms and a
comparison that is a quasi-isomorphism on every graded piece and a strict
monomorphism in every degree. -/
theorem exists_strictInjectiveResolution (a : ℤ) (K : CochainComplex (category C) ℤ)
    (hK : K.IsStrictlyGE a) :
    ∃ (I : CochainComplex (category C) ℤ) (α : K ⟶ I),
      I.IsStrictlyGE a ∧
      (∀ n : ℤ, IsFilteredInjective (I.X n)) ∧
      (∀ p : ℤ, QuasiIso
        (((gradedPieceFunctor (C := C) p).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      ∀ n : ℤ, IsStrictMono (α.f n) := sorry

end CategoryTheory.FiniteFilteredDiagram
