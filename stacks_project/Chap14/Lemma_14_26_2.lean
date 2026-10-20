module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.DeltaOne.Homotopy
import StacksCheckRecall

/-!
@stack 019L

# Source-facing recall for Lemma 14.26.2

The degreewise maps and all endpoint, face, and degeneracy identities in the lemma are precisely
the data and laws of mathlib's canonical `SimplicialObject.Homotopy` structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
variable {X Y : SimplicialObject C} (a b : X ⟶ Y)

/- Lemma 14.26.2 (1): the canonical owner packages the degreewise homotopy maps and their
endpoint identities. -/
@[stacks 019L "Lemma 14.26.2 (1): canonical package"]
#check (Homotopy a b)

variable (H : Homotopy a b)

section Endpoints

variable (n : ℕ) (i : Fin (n + 1))

/- Lemma 14.26.2 (1): the basic data in degree `n` are the maps indexed by
`i : Fin (n + 1)`. -/
@[stacks 019L "Lemma 14.26.2 (1): degreewise maps"]
#check (H.h i : X _⦋n⦌ ⟶ Y _⦋n + 1⦌)

/- Lemma 14.26.2 (1): the zero endpoint recovers `b` in degree `n`. -/
@[stacks 019L "Lemma 14.26.2 (1): zero endpoint"]
#check (H.h_zero_comp_δ_zero n : H.h 0 ≫ Y.δ 0 = b.app (op ⦋n⦌))

/- Lemma 14.26.2 (1): the final endpoint recovers `a` in degree `n`. -/
@[stacks 019L "Lemma 14.26.2 (1): final endpoint"]
#check (H.h_last_comp_δ_last n :
  H.h (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = a.app (op ⦋n⦌))

end Endpoints

section Faces

variable {n : ℕ}

/- Lemma 14.26.2 (2): before the homotopy index, a face commutes past the
degreewise homotopy map. -/
@[stacks 019L "Lemma 14.26.2 (2): face before the homotopy index"]
#check (fun (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) ↦
  (H.h_succ_comp_δ_castSucc_of_lt i j hij :
    H.h j.succ ≫ Y.δ i.castSucc = X.δ i ≫ H.h j))

/- Lemma 14.26.2 (2): the adjacent face values agree at the boundary of the
same source relation. -/
@[stacks 019L "Lemma 14.26.2 (2): adjacent face values"]
#check (fun (j : Fin (n + 1)) ↦
  (H.h_succ_comp_δ_castSucc_succ j :
    H.h j.succ ≫ Y.δ j.castSucc.succ =
      H.h j.castSucc ≫ Y.δ j.castSucc.succ))

/- Lemma 14.26.2 (3): after the homotopy index, a face commutes past the
degreewise homotopy map. -/
@[stacks 019L "Lemma 14.26.2 (3): face after the homotopy index"]
#check (fun (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) ↦
  (H.h_castSucc_comp_δ_succ_of_lt i j hji :
    H.h j.castSucc ≫ Y.δ i.succ = X.δ i ≫ H.h j))

end Faces

section Degeneracies

variable {n : ℕ}

/- Lemma 14.26.2 (4): before the homotopy index, a degeneracy commutes past the
degreewise homotopy map. -/
@[stacks 019L "Lemma 14.26.2 (4): degeneracy before the homotopy index"]
#check (fun (i j : Fin (n + 1)) (hij : i ≤ j) ↦
  (H.h_comp_σ_castSucc_of_le i j hij :
    H.h j ≫ Y.σ i.castSucc = X.σ i ≫ H.h j.succ))

/- Lemma 14.26.2 (5): after the homotopy index, a degeneracy commutes past the
degreewise homotopy map. -/
@[stacks 019L "Lemma 14.26.2 (5): degeneracy after the homotopy index"]
#check (fun (i j : Fin (n + 1)) (hji : j ≤ i) ↦
  (H.h_comp_σ_succ_of_lt i j hji :
    H.h j ≫ Y.σ i.succ = X.σ i ≫ H.h j.castSucc))

end Degeneracies

section Constructor

variable
  (h : ∀ {n : ℕ}, Fin (n + 1) → (X _⦋n⦌ ⟶ Y _⦋n + 1⦌))
  (hZero : ∀ n : ℕ, h 0 ≫ Y.δ 0 = b.app (op ⦋n⦌))
  (hLast : ∀ n : ℕ,
    h (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = a.app (op ⦋n⦌))
  (hFaceBefore : ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)),
    i ≤ j.castSucc → h j.succ ≫ Y.δ i.castSucc = X.δ i ≫ h j)
  (hFaceAdjacent : ∀ {n : ℕ} (j : Fin (n + 1)),
    h j.succ ≫ Y.δ j.castSucc.succ = h j.castSucc ≫ Y.δ j.castSucc.succ)
  (hFaceAfter : ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)),
    j.castSucc < i → h j.castSucc ≫ Y.δ i.succ = X.δ i ≫ h j)
  (hDegBefore : ∀ {n : ℕ} (i j : Fin (n + 1)),
    i ≤ j → h j ≫ Y.σ i.castSucc = X.σ i ≫ h j.succ)
  (hDegAfter : ∀ {n : ℕ} (i j : Fin (n + 1)),
    j ≤ i → h j ≫ Y.σ i.succ = X.σ i ≫ h j.castSucc)

/- Lemma 14.26.2 (6): conversely, degreewise maps satisfying (1)--(5) assemble into the
canonical simplicial homotopy. -/
@[stacks 019L "Lemma 14.26.2 (6): converse constructor"]
#check (Homotopy.mk h hZero hLast hFaceBefore hFaceAdjacent hFaceAfter hDegBefore hDegAfter :
  Homotopy a b)

/- Lemma 14.26.2 (6): the canonical package assembled from (1)--(5) reconstructs the actual
cylinder morphism and both endpoint equations from Definition 14.26.1. -/
@[stacks 019L "Lemma 14.26.2 (6): cylinder reconstruction"]
#check (copower.deltaOne.Homotopy.ofCombinatorial
    (Homotopy.mk h hZero hLast hFaceBefore hFaceAdjacent hFaceAfter hDegBefore hDegAfter) :
  copower.deltaOne.Homotopy a b)

end Constructor

end CategoryTheory.SimplicialObject
