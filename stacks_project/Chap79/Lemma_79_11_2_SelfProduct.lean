/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.CategoryTheory.Limits.Over.Products
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Self-products of the projective line as algebraic spaces

The `n`-fold self-product `(P¹_k)^n` of the projective line over a field `k`,
viewed as an algebraic space over `Spec k`, together with its coordinate
projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The `n`-fold self-product of `P¹` over `Spec k`, as an algebraic space. -/
def projectiveLineSelfProduct (k : Type u) [Field k] (n : ℕ) :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  ofOver (piObj (fun _ : Fin n ↦ ProjectiveSpace.schemeOver k 1))

/-- `projectiveLineSelfProduct k n` is `ofOver` of the finite product of `n`
copies of `ProjectiveSpace.schemeOver k 1` in `Over (Spec k)`. -/
theorem projectiveLineSelfProduct_eq (k : Type u) [Field k] (n : ℕ) :
    projectiveLineSelfProduct k n =
      ofOver (piObj (fun _ : Fin n ↦ ProjectiveSpace.schemeOver k 1)) :=
  sorry

/-- The morphism `(P¹_k)^n ⟶ (P¹_k)^m` induced by reindexing the factors along
`e : Fin m → Fin n`. -/
def projectiveLineSelfProductπ (k : Type u) [Field k] {n m : ℕ}
    (e : Fin m → Fin n) :
    projectiveLineSelfProduct k n ⟶ projectiveLineSelfProduct k m :=
  ofOverMap (Pi.lift fun j ↦ Pi.π (fun _ : Fin n ↦ ProjectiveSpace.schemeOver k 1) (e j))

/-- The identity reindexing induces the identity on `projectiveLineSelfProduct k n`. -/
theorem projectiveLineSelfProductπ_id {k : Type u} [Field k] {n : ℕ} :
    projectiveLineSelfProductπ k (id : Fin n → Fin n) =
      𝟙 (projectiveLineSelfProduct k n) :=
  sorry

/-- Coordinate projections are functorial in the reindexing map. -/
theorem projectiveLineSelfProductπ_comp {k : Type u} [Field k] {n m l : ℕ}
    (e : Fin m → Fin n) (e' : Fin l → Fin m) :
    projectiveLineSelfProductπ k (e ∘ e') =
      projectiveLineSelfProductπ k e ≫ projectiveLineSelfProductπ k e' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
