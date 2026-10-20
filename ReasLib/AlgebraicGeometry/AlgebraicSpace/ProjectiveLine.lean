module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Self-products of the projective line as algebraic spaces

Finite self-products of the projective line over a field have canonical coordinate
projections. Morphisms from nonempty self-products to separated finite-type
algebraic spaces factor through such projections followed by finite morphisms.
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
  rfl

/-- The morphism `(P¹_k)^n ⟶ (P¹_k)^m` induced by reindexing the factors along
`e : Fin m → Fin n`. -/
def projectiveLineSelfProductπ (k : Type u) [Field k] {n m : ℕ}
    (e : Fin m → Fin n) :
    projectiveLineSelfProduct k n ⟶ projectiveLineSelfProduct k m :=
  SchemeRealization.ofOverMap
    (Pi.lift fun j ↦ Pi.π (fun _ : Fin n ↦ ProjectiveSpace.schemeOver k 1) (e j))

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

/-- Every morphism from a nonempty finite self-product of the projective line over a field
to a separated finite-type algebraic space factors as a projection selecting distinct
coordinates followed by a finite morphism. The retained product may have zero factors. -/
theorem exists_isFinite_factor_of_projectiveLineSelfProduct
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n)
    {Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Separated (SchemeRealization.toBase Z)] [FiniteType (SchemeRealization.toBase Z)]
    (f : projectiveLineSelfProduct k n ⟶ Z) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin n) (g : projectiveLineSelfProduct k m ⟶ Z),
      IsFinite g ∧ projectiveLineSelfProductπ k (e : Fin m → Fin n) ≫ g = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
