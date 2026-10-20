/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ComposableArrows.Property
public import ReasLib.CategoryTheory.ComposableArrows.Snoc.Hom
public import ReasLib.Algebra.Homology.HomologicalComplex.TermwiseSplit
public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitMonoFactorization
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite split-monomorphic homotopy replacements

This leaf owns the reusable statement behind finite ladder replacement arguments. The conclusion
is expressed through the canonical `ComposableArrows` property views and the shape-independent
`HomologicalComplex.termwiseSplitMono` morphism property. A pointwise source-facing formulation
is also provided below for applications whose hypotheses and conclusions are indexed explicitly.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe v u

namespace CategoryTheory
namespace ComposableArrows

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable [HasBinaryBiproducts 𝒜]

/-- Reusable data for a finite split-monomorphic homotopy replacement.

The owner separates the replacement and its comparison from their structural properties, so
downstream constructions can consume the data through projections without unpacking a nested
existential statement. -/
@[stacks 014M "finite split-monomorphic homotopy replacement data"]
structure SplitMonoReplacement {n : ℕ}
    (S : ComposableArrows (CochainComplex 𝒜 ℤ) n) where
  /-- The finite sequence replacing the source sequence. -/
  target : ComposableArrows (CochainComplex 𝒜 ℤ) n
  /-- The componentwise homotopy-equivalence comparison with the source sequence. -/
  comparison : target ⟶ S
  /-- Every successor map in the replacement is termwise a split monomorphism. -/
  arrowProperty :
    ComposableArrows.arrowProperty (HomologicalComplex.termwiseSplitMono 𝒜 (up ℤ)) target
  /-- Every component of the comparison is a homotopy equivalence. -/
  componentProperty :
    ComposableArrows.componentProperty
      (HomologicalComplex.homotopyEquivalences 𝒜 (up ℤ)) comparison
  /-- Bounded-below cochain complexes remain bounded below after replacement. -/
  plus : objectProperty (CochainComplex.plus 𝒜) S →
    objectProperty (CochainComplex.plus 𝒜) target
  /-- Bounded-above cochain complexes remain bounded above after replacement. -/
  minus : objectProperty (CochainComplex.minus 𝒜) S →
    objectProperty (CochainComplex.minus 𝒜) target
  /-- Bounded cochain complexes remain bounded after replacement. -/
  bounded : objectProperty (CochainComplex.bounded 𝒜) S →
    objectProperty (CochainComplex.bounded 𝒜) target

/-- Every finite sequence of cochain complexes has split-monomorphic homotopy replacement data. -/
@[stacks 014M "existence of finite split-monomorphic homotopy replacement data"]
theorem SplitMonoReplacement.nonempty
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n) :
    Nonempty (SplitMonoReplacement S) := sorry

/-- Lemma 13.9.15: every finite composable sequence of cochain complexes admits a comparison
row whose successor maps are termwise split monomorphisms and whose component maps are homotopy
equivalences.  The three standard boundedness properties are preserved termwise. -/
@[stacks 014M "finite split-monomorphic homotopy replacement"]
theorem exists_splitMonoReplacement
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n) :
    ∃ (T : ComposableArrows (CochainComplex 𝒜 ℤ) n) (φ : T ⟶ S),
      arrowProperty (HomologicalComplex.termwiseSplitMono 𝒜 (up ℤ)) T ∧
      componentProperty (HomologicalComplex.homotopyEquivalences 𝒜 (up ℤ)) φ ∧
      (objectProperty (CochainComplex.plus 𝒜) S →
        objectProperty (CochainComplex.plus 𝒜) T) ∧
      (objectProperty (CochainComplex.minus 𝒜) S →
        objectProperty (CochainComplex.minus 𝒜) T) ∧
      (objectProperty (CochainComplex.bounded 𝒜) S →
        objectProperty (CochainComplex.bounded 𝒜) T) := sorry

/-- Pointwise source-facing form of `exists_splitMonoReplacement`.

This bridge expands the reusable property views into the explicitly indexed conditions used by
finite ladder arguments. -/
@[stacks 014M "pointwise bridge for finite homotopy replacement"]
theorem exists_splitMono_homotopyReplacement
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n) :
    ∃ (T : ComposableArrows (CochainComplex 𝒜 ℤ) n) (φ : T ⟶ S),
      (∀ i : Fin n, ∀ k : ℤ, IsSplitMono ((T.map' i.1 (i.1 + 1)).f k)) ∧
      (∀ i : Fin (n + 1), homotopyEquivalences 𝒜 (up ℤ) (φ.app i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (T.obj i)) := sorry

end ComposableArrows
end CategoryTheory
