module

public import ReasLib.AlgebraicGeometry.ChernClass.ChernCharacter
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass.ChernCharacter

/-- The second Adams operation multiplies the degree-`i` coefficient of a Chern character
by `2 ^ i`. -/
theorem coeff_adamsTwo
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)] [∀ X, Algebra ℚ (A.obj (Opposite.op X))]
    (S : CohomologyTheory toScheme A Agrade)
    (ch : ChernCharacter toScheme A Agrade S.firstChernClass)
    (X : C) (α : Scheme.VectorBundleK0 (toScheme.obj X)) (i : ℕ) :
    PowerSeries.coeff i
        (ch.app X (Scheme.VectorBundleK0.adamsTwo (toScheme.obj X) α)) =
      (2 ^ i : ℕ) • PowerSeries.coeff i (ch.app X α) := sorry

end AlgebraicGeometry.ChernClass.ChernCharacter
