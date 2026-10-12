/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.PuncturedProduct
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

universe u

/- Lemma 110.34.4: Let k be a field. Let Cᵢ, i = 1, …, n be smooth, projective,
geometrically irreducible curves over k. Let Pᵢ be a rational point of Cᵢ and let Qᵢ be a
point of Cᵢ with residue degree 2. Then the class of P₁ × ⋯ × Pₙ is nonzero in
CH₀(U₁ ×_k ⋯ ×_k Uₙ), where Uᵢ = Cᵢ \ {Qᵢ}. -/
@[stacks 05WK] #check (AlgebraicGeometry.ChowGroup.puncturedProduct_rationalPointClass_ne_zero :
    ∀ {k : Type u} [Field k] {n : ℕ} (C : Fin n → SchemeOverField k)
    [∀ i, Curve (C i)] [∀ i, Smooth (C i).hom] [∀ i, Projective (C i).hom]
    [∀ i, GeometricallyIrreducible (C i).hom]
    (P : (i : Fin n) → 𝟙_ (SchemeOverField k) ⟶ C i)
    (Q : (i : Fin n) → (C i).left)
    (hQ : ∀ i, (C i).hom.residueDegree (Q i) = 2),
    ChowGroup.Localization.openPullback (∏ᶜ C).hom (fun _ ↦ (0 : ℤ))
      (SchemeOverField.puncturedProductOpen C Q) 0
      (ChowGroup.rationalPointClass (∏ᶜ C) (Pi.lift P)) ≠ 0)
