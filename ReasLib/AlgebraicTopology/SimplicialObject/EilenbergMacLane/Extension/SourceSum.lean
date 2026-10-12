/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.SourceIndex
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Sum
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0192

# Degreewise source-oriented Eilenberg--MacLane extension sums

The underlying extension object is the same `Γ₀` object as in `Extension.Sum`.  Only the labels of
its two-family coproduct are reversed here, so the source-facing inclusion and structure-map
formulas can be used without unfolding the `d₀` convention.  The coproduct isomorphism is
transported along `Index.revEquiv`; no second coproduct construction is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.extension.source

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
variable [HasFiniteCoproducts 𝒜]

/-- The coefficient inclusion indexed by a source-oriented extension index. -/
@[stacks 0192 "source-oriented extension summand inclusion"]
noncomputable def inclusion (A : 𝒜) {k n : ℕ} (a : Index k n) :
    A ⟶ (extension.object A k).obj (Opposite.op ⦋n⦌) :=
  extension.sum.inclusion A (Index.rev a)

/-- Reversing a source index recovers the corresponding canonical summand inclusion. -/
@[simp, stacks 0192 "source and d₀ extension summand inclusion comparison"]
theorem inclusion.rev (A : 𝒜) {k n : ℕ} (a : Index k n) :
    inclusion A (Index.rev a) = extension.sum.inclusion A a := sorry

namespace simplex

/-- A coefficient morphism commutes with a source-oriented summand inclusion. -/
@[stacks 0192 "source-oriented extension summand coefficient naturality"]
theorem inclusion.naturality {k n : ℕ} (a : Index k n) {A B : 𝒜} (f : A ⟶ B) :
    f ≫ source.inclusion B a =
      source.inclusion A a ≫ (extension.sum.simplex.functor (𝒜 := 𝒜) k n).map f := sorry

/-- The natural source-oriented summand inclusion. -/
@[stacks 0192 "natural source-oriented extension summand inclusion"]
noncomputable def inclusion {k n : ℕ} (a : Index k n) :
    𝟭 𝒜 ⟶ extension.sum.simplex.functor (𝒜 := 𝒜) k n where
  app A := source.inclusion A a
  naturality _ _ f := inclusion.naturality a f

/-- The component of the natural source-oriented summand inclusion. -/
@[simp, stacks 0192 "natural source-oriented extension summand inclusion component"]
theorem inclusion.app {k n : ℕ} (a : Index k n) (A : 𝒜) :
    (inclusion (𝒜 := 𝒜) a).app A = source.inclusion A a := sorry

end simplex

/-- The source-oriented degreewise coproduct reindexing isomorphism. -/
@[stacks 0192 "source-oriented extension coproduct decomposition"]
noncomputable def iso (A : 𝒜) (k n : ℕ) :
    (extension.object A k).obj (Opposite.op ⦋n⦌) ≅
      ∐ fun _ : Index k n ↦ A where
  hom :=
    (extension.sum.iso A k n).hom ≫
      (Sigma.reindex (Index.revEquiv (k := k) (n := n))
        (fun _ : Index k n ↦ A)).inv
  inv :=
    (Sigma.reindex (Index.revEquiv (k := k) (n := n))
        (fun _ : Index k n ↦ A)).hom ≫
      (extension.sum.iso A k n).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The source-oriented decomposition sends each source summand to its canonical coproduct leg. -/
@[simp, stacks 0192 "source-oriented extension decomposition on summands"]
theorem iso.inclusion_hom (A : 𝒜) {k n : ℕ} (a : Index k n) :
    inclusion A a ≫ (iso A k n).hom =
      Sigma.ι (fun _ : Index k n ↦ A) a := sorry

/-- The inverse source-oriented decomposition sends a canonical coproduct leg to its source
summand inclusion. -/
@[simp, stacks 0192 "inverse source-oriented extension decomposition on summands"]
theorem iso.inclusion_inv (A : 𝒜) {k n : ℕ} (a : Index k n) :
    Sigma.ι (fun _ : Index k n ↦ A) a ≫ (iso A k n).inv =
      inclusion A a := sorry

/-- The forward source-oriented coproduct decomposition is natural in the coefficient object. -/
@[stacks 0192 "source-oriented extension coproduct forward naturality"]
theorem iso.hom_naturality (k n : ℕ) {A B : 𝒜} (f : A ⟶ B) :
    (extension.sum.simplex.functor (𝒜 := 𝒜) k n).map f ≫ (iso B k n).hom =
      (iso A k n).hom ≫
        (Sigma.diagonal (C := 𝒜) (Index k n)).map f := sorry

/-- The inverse source-oriented coproduct decomposition is natural in the coefficient object. -/
@[stacks 0192 "source-oriented extension coproduct inverse naturality"]
theorem iso.inv_naturality (k n : ℕ) {A B : 𝒜} (f : A ⟶ B) :
    (Sigma.diagonal (C := 𝒜) (Index k n)).map f ≫ (iso B k n).inv =
      (iso A k n).inv ≫
        (extension.sum.simplex.functor (𝒜 := 𝒜) k n).map f := sorry

/-- In fixed simplicial degree, the source-oriented extension functor is naturally isomorphic to
the coproduct of its source-labeled coefficient summands. -/
@[stacks 0192 "natural source-oriented extension coproduct decomposition"]
noncomputable def natIso (k n : ℕ) :
    extension.sum.simplex.functor (𝒜 := 𝒜) k n ≅
      Sigma.diagonal (C := 𝒜) (Index k n) :=
  NatIso.ofComponents (fun A ↦ iso A k n)
    (fun f ↦ iso.hom_naturality k n f)

/-- The component of the source-oriented coefficient decomposition is its objectwise isomorphism. -/
@[simp, stacks 0192 "source-oriented coefficient decomposition component"]
theorem natIso.app (k n : ℕ) (A : 𝒜) :
    (natIso (𝒜 := 𝒜) k n).app A = iso A k n := sorry

/-- The forward component of the source-oriented coefficient decomposition. -/
@[simp, stacks 0192 "source-oriented coefficient decomposition forward component"]
theorem natIso.hom_app (k n : ℕ) (A : 𝒜) :
    (natIso (𝒜 := 𝒜) k n).hom.app A = (iso A k n).hom := sorry

/-- The inverse component of the source-oriented coefficient decomposition. -/
@[simp, stacks 0192 "source-oriented coefficient decomposition inverse component"]
theorem natIso.inv_app (k n : ℕ) (A : 𝒜) :
    (natIso (𝒜 := 𝒜) k n).inv.app A = (iso A k n).inv := sorry

/-- The source-oriented coefficient decomposition sends a natural summand inclusion to its
canonical coproduct leg. -/
@[simp, stacks 0192 "source-oriented natural decomposition on summand inclusions"]
theorem natIso.inclusion_hom {k n : ℕ} (a : Index k n) :
    simplex.inclusion (𝒜 := 𝒜) a ≫ (natIso (𝒜 := 𝒜) k n).hom =
      Sigma.diagonal.ι (C := 𝒜) a := sorry

/-- The inverse source-oriented coefficient decomposition sends a coproduct leg to its natural
source summand inclusion. -/
@[simp, stacks 0192 "inverse source-oriented natural decomposition on summand inclusions"]
theorem natIso.inclusion_inv {k n : ℕ} (a : Index k n) :
    Sigma.diagonal.ι (C := 𝒜) a ≫ (natIso (𝒜 := 𝒜) k n).inv =
      simplex.inclusion (𝒜 := 𝒜) a := sorry

/-- The source-oriented structure map sends a summand along `last.pull`, or to zero when absent. -/
@[stacks 0192 "source-oriented extension structure map on summands"]
theorem inclusion.map (A : 𝒜) {k m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : Index k n) :
    inclusion A a ≫ (extension.object A k).map φ.op =
      Option.elim (Index.last.pull a φ) 0 (fun b ↦ inclusion A b) := sorry

/-- A successful source-oriented pull gives the corresponding summand map formula. -/
@[simp, stacks 0192 "successful source-oriented extension structure map"]
theorem inclusion.map_of_some (A : 𝒜) {k m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : Index k n) {b : Index k m}
    (h : Index.last.pull a φ = some b) :
    inclusion A a ≫ (extension.object A k).map φ.op = inclusion A b := sorry

/-- An absent source-oriented pull kills the corresponding summand. -/
@[simp, stacks 0192 "absent source-oriented extension structure map"]
theorem inclusion.map_of_none (A : 𝒜) {k m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : Index k n)
    (h : Index.last.pull a φ = none) :
    inclusion A a ≫ (extension.object A k).map φ.op = 0 := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.extension.source
