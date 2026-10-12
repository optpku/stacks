/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Factorization
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Truncation Factorizations for Finite Composable Chains

This leaf isolates the reusable part of the stepwise truncation argument.  The core statements
live on composable arrows in the derived category; the cochain-complex statements below are thin
bridges through `DerivedCategory.Q`.  The starting degree is an explicit integer parameter, so the
same API applies after shifts and is not tied to a degree-zero presentation.
-/

open CategoryTheory
open CategoryTheory.ComposableArrows
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

namespace DerivedCategory.Truncation

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

namespace ComposableArrows

/-- Stacks 08Q2: a chain whose left endpoint satisfies `S.left.IsLE a` and vanishes successively on the
corresponding homology groups factors through the lower truncation at `a - n`. -/
@[stacks 08Q2 "derived truncation factorization"]
theorem exists_truncLE
    {a : ℤ} {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.left.IsLE a)
    (hstep : ∀ j (hj : j < n),
      (DerivedCategory.homologyFunctor 𝒜 (a - (j : ℤ))).map (S.arrow j hj).hom = 0) :
    ∃ φ : S.left ⟶ (t.truncLE (a - (n : ℤ))).obj S.right,
      φ ≫ (t.truncLEι (a - (n : ℤ))).app S.right = S.hom := sorry

/-- Stacks 08Q2: a chain whose right endpoint satisfies `S.right.IsGE a` and vanishes successively on the
corresponding homology groups factors through the upper truncation at `a + n`. -/
@[stacks 08Q2 "derived truncation factorization"]
theorem exists_truncGE
    {a : ℤ} {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.right.IsGE a)
    (hstep : ∀ j (hj : j < n),
      (DerivedCategory.homologyFunctor 𝒜 (a + ((n - (j + 1) : ℕ) : ℤ))).map
        (S.arrow j hj).hom = 0) :
    ∃ φ : (t.truncGE (a + (n : ℤ))).obj S.left ⟶ S.right,
      (t.truncGEπ (a + (n : ℤ))).app S.left ≫ φ = S.hom := sorry

namespace Cochain

/-- Stacks 08Q2: the cochain-complex form of lower-truncation factorization, obtained by
applying the derived-category theorem to `DerivedCategory.Q`. -/
@[stacks 08Q2 "cochain-complex truncation bridge"]
theorem exists_truncLE
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n)
    (h₀ : (DerivedCategory.Q.obj S.left).IsLE 0)
    (hstep : ∀ j (hj : j < n),
      (DerivedCategory.homologyFunctor 𝒜 (-(j : ℤ))).map
          (DerivedCategory.Q.map ((S.arrow j hj).hom)) = 0) :
    ∃ φ :
      DerivedCategory.Q.obj S.left ⟶
        (t.truncLE (-(n : ℤ))).obj (DerivedCategory.Q.obj S.right),
      φ ≫ (t.truncLEι (-(n : ℤ))).app (DerivedCategory.Q.obj S.right) =
        DerivedCategory.Q.map S.hom := sorry

/-- Stacks 08Q2: the cochain-complex form of upper-truncation factorization, obtained by
applying the derived-category theorem to `DerivedCategory.Q`. -/
@[stacks 08Q2 "cochain-complex truncation bridge"]
theorem exists_truncGE
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    {n : ℕ} (S : ComposableArrows (CochainComplex 𝒜 ℤ) n)
    (h₀ : (DerivedCategory.Q.obj S.right).IsGE 0)
    (hstep : ∀ j (hj : j < n),
      (DerivedCategory.homologyFunctor 𝒜 ((n - (j + 1) : ℕ) : ℤ)).map
          (DerivedCategory.Q.map ((S.arrow j hj).hom)) = 0) :
    ∃ φ :
      (t.truncGE (n : ℤ)).obj (DerivedCategory.Q.obj S.left) ⟶
        DerivedCategory.Q.obj S.right,
      (t.truncGEπ (n : ℤ)).app (DerivedCategory.Q.obj S.left) ≫ φ =
        DerivedCategory.Q.map S.hom := sorry

end Cochain

end ComposableArrows

end DerivedCategory.Truncation

end CategoryTheory
