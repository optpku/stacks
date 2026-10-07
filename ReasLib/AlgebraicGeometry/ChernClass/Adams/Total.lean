module

public import ReasLib.AlgebraicGeometry.ChernClass.Total
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass.TotalChernClass

/-- The second Adams operation multiplies the degree-`i` coefficient of a total Chern class
by `2 ^ i`. -/
theorem coeff_adamsTwo
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)] (S : Theory toScheme A Agrade)
    (c : TotalChernClass toScheme A Agrade S.firstChernClass)
    (X : C) (α : Scheme.VectorBundleK0 (toScheme.obj X)) (i : ℕ) :
    PowerSeries.coeff i
        (c.app X (Scheme.VectorBundleK0.adamsTwo (toScheme.obj X) α)) =
      (2 ^ i : ℕ) • PowerSeries.coeff i (c.app X α) := sorry

end AlgebraicGeometry.ChernClass.TotalChernClass
