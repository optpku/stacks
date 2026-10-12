/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Index
public import ReasLib.AlgebraicTopology.SimplexCategory.Snoc
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-oriented Eilenberg--MacLane extension indices

@stack 0192

The inverse Dold--Kan functor `Γ₀` uses the initial-face (`d₀`) normalization internally.  The
source presentation of the Eilenberg--MacLane extension uses the opposite endpoint of a simplex:
the lower summands are followed by `δ (Fin.last (k + 1))`.  This leaf owns the source-facing
index and partial-pull API by transporting the canonical `Index` API across simplex reversal.
It deliberately does not introduce a second extension object or a transparent alias for `Index`.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.extension

namespace Index

/-- Reverse both epi families in an extension index. -/
@[stacks 0192 "source-oriented reversal of extension indices"]
def rev {k n : ℕ} : Index k n → Index k n
  | .inl a => .inl (SimplexCategory.EpiHom.rev a)
  | .inr a => .inr (SimplexCategory.EpiHom.rev a)

/-- Reversal preserves the lower extension-index family and reverses its epimorphism. -/
@[simp, stacks 0192 "reversal of a lower extension index"]
theorem rev_lower {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k⦌) :
    rev (Index.lower a) = Index.lower (SimplexCategory.EpiHom.rev a) := sorry

/-- Reversal preserves the upper extension-index family and reverses its epimorphism. -/
@[simp, stacks 0192 "reversal of an upper extension index"]
theorem rev_upper {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k + 1⦌) :
    rev (Index.upper a) = Index.upper (SimplexCategory.EpiHom.rev a) := sorry

/-- Reversal of an extension index is involutive. -/
@[simp, stacks 0192 "involutivity of source-oriented extension-index reversal"]
theorem rev_rev {k n : ℕ} (a : Index k n) :
    rev (rev a) = a := sorry

/-- The source-oriented extension indices form an involutive equivalence. -/
@[stacks 0192 "source-oriented extension-index reversal equivalence"]
def revEquiv {k n : ℕ} : Index k n ≃ Index k n where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

namespace last

/-- The common map represented by a source-oriented extension index.

The lower family uses the final coface, while the upper family is already indexed by
epimorphisms onto `[k + 1]`. -/
@[stacks 0192 "source-oriented Eilenberg-MacLane extension index map"]
def hom {k n : ℕ} : Index k n → (⦋n⦌ ⟶ ⦋k + 1⦌)
  | .inl a => a.hom ≫ SimplexCategory.δ (Fin.last (k + 1))
  | .inr a => a.hom

/-- The source-oriented map is the reversal of the canonical `d₀`-oriented map. -/
@[stacks 0192 "source and d₀ extension-index map comparison"]
theorem hom_rev {k n : ℕ} (a : Index k n) :
    hom a = SimplexCategory.rev.map (Index.hom (Index.rev a)) := sorry

/-- The lower source-oriented summand map uses the final coface. -/
@[simp, stacks 0192 "source-oriented lower extension summand map"]
theorem hom_lower {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k⦌) :
    hom (Index.lower a) = a.hom ≫ SimplexCategory.δ (Fin.last (k + 1)) := sorry

/-- The upper source-oriented summand map is its indexing epimorphism. -/
@[simp, stacks 0192 "source-oriented upper extension summand map"]
theorem hom_upper {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k + 1⦌) :
    hom (Index.upper a) = a.hom := sorry

/-- A source-oriented extension index is determined by its represented map to `[k + 1]`. -/
@[stacks 0192 "source-oriented extension summand index injectivity"]
theorem hom_injective {k n : ℕ} :
    Function.Injective (hom (k := k) (n := n)) := sorry

/-- Adjoining the terminal source vertex to the common source-oriented map is epic. -/
@[stacks 0192 "epic terminal extension of a source-oriented extension index"]
theorem snoc_epi {k n : ℕ} (a : Index k n) :
    Epi (SimplexCategory.Hom.snoc (hom a)) := sorry

/-- Append the terminal source vertex to a source-oriented extension index. -/
@[stacks 0192 "terminal extension of a source-oriented extension index"]
def snoc {k n : ℕ} (a : Index k n) : Index k (n + 1) :=
  Index.upper ⟨SimplexCategory.Hom.snoc (hom a), snoc_epi a⟩

/-- The map represented by a terminally extended source-oriented index. -/
@[simp, stacks 0192 "map of a terminally extended source-oriented index"]
theorem hom_snoc {k n : ℕ} (a : Index k n) :
    hom (snoc a) = SimplexCategory.Hom.snoc (hom a) := sorry

/-- Pull a source-oriented extension index along a simplex operator.

This is the canonical partial pull transported across `SimplexCategory.rev`; `none` means that
the corresponding summand is sent to zero. -/
@[stacks 0192 "source-oriented partial reindexing of extension summands"]
noncomputable def pull {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) : Option (Index k m) :=
  Option.map Index.rev
    (Index.pull (Index.rev a) (SimplexCategory.rev.map φ))

namespace pull

/-- Reversing a canonical pull gives the source-oriented pull along the reversed simplex map. -/
@[simp, stacks 0192 "source and d₀ extension-index pull comparison"]
theorem rev {k m n : ℕ} (a : Index k n) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    last.pull (Index.rev a) (SimplexCategory.rev.map φ) =
      Option.map Index.rev (Index.pull a φ) := sorry

/-- A successful source-oriented pull represents the composite source-oriented map. -/
@[stacks 0192 "successful source-oriented extension-index pull formula"]
theorem hom {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) {b : Index k m}
    (h : last.pull a φ = some b) :
    last.hom b = φ ≫ last.hom a := sorry

/-- A source-oriented pull succeeds exactly for an index representing the composite map. -/
@[simp, stacks 0192 "source-oriented extension-index pull criterion"]
theorem eq_some_iff {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (b : Index k m) :
    last.pull a φ = some b ↔ last.hom b = φ ≫ last.hom a := sorry

/-- A source-oriented pull is absent exactly when no index represents the composite map. -/
@[simp, stacks 0192 "source-oriented zero extension-index pull criterion"]
theorem eq_none_iff {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    last.pull a φ = none ↔
      ¬ ∃ b : Index k m, last.hom b = φ ≫ last.hom a := sorry

/-- A successful source-oriented pull has a unique result. -/
@[stacks 0192 "uniqueness of a source-oriented extension-index pull"]
theorem unique {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) {b c : Index k m}
    (hb : last.pull a φ = some b) (hc : last.pull a φ = some c) :
    b = c := sorry

/-- Pulling a source-oriented index along an identity leaves it unchanged. -/
@[simp, stacks 0192 "identity law for source-oriented extension-index pulls"]
theorem id {k n : ℕ} (a : Index k n) :
    last.pull a (𝟙 _) = some a := sorry

/-- Source-oriented extension-index pulls respect composition. -/
@[stacks 0192 "composition law for source-oriented extension-index pulls"]
theorem comp {k l m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (ψ : ⦋l⦌ ⟶ ⦋m⦌) :
    last.pull a (ψ ≫ φ) =
      (last.pull a φ).bind fun b ↦ last.pull b ψ := sorry

end pull

end last

end Index

end CategoryTheory.SimplicialObject.eilenbergMacLane.extension
