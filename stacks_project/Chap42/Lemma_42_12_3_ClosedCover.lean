module

public import ReasLib.AlgebraicGeometry.CycleGroup.ClosedCover

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.ClosedCover

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
variable (Z₁ Z₂ : X.IdealSheafData) (k : ℤ)

/- Compatibility check for the signed intersection pushforward. -/
#check (intersectionMap p δ Z₁ Z₂ k :
  CycleGroup (Scheme.schemeTheoreticIntersection Z₁ Z₂)
      (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) k →+
    CycleGroup Z₁.subscheme
        ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k ×
      CycleGroup Z₂.subscheme
        ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k)

/- Compatibility check for evaluation of the signed intersection pushforward. -/
#check (intersectionMap_apply p δ Z₁ Z₂ k :
  ∀ c : CycleGroup (Scheme.schemeTheoreticIntersection Z₁ Z₂)
      (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) k,
    intersectionMap p δ Z₁ Z₂ k c =
      (CycleGroup.mapHom
          (Scheme.IdealSheafData.inclusion (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂))
          (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ)
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k c,
        -CycleGroup.mapHom
          (Scheme.IdealSheafData.inclusion (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂))
          (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ)
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k c))

/- Compatibility check for the sum of the two ambient pushforwards. -/
#check (coverMap p δ Z₁ Z₂ k :
  (CycleGroup Z₁.subscheme
      ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k ×
    CycleGroup Z₂.subscheme
      ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k) →+
    CycleGroup X (p.relativeDimensionFunction δ) k)

/- Compatibility check for evaluation of the sum of ambient pushforwards. -/
#check (coverMap_apply p δ Z₁ Z₂ k :
  ∀ c : CycleGroup Z₁.subscheme
      ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k ×
    CycleGroup Z₂.subscheme
      ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k,
    coverMap p δ Z₁ Z₂ k c =
      CycleGroup.mapHom Z₁.subschemeι
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ)
          (p.relativeDimensionFunction δ) k c.1 +
        CycleGroup.mapHom Z₂.subschemeι
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ)
          (p.relativeDimensionFunction δ) k c.2)

/- Compatibility check for the zero-composite law. -/
#check (intersectionMap_comp_coverMap p δ Z₁ Z₂ k :
  AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k) ≫
    AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k) = 0)

/- Compatibility check for the closed-cover short complex. -/
#check (complex p δ Z₁ Z₂ k : ShortComplex Ab)

/- Compatibility check for the first arrow of the closed-cover short complex. -/
#check (complex_f p δ Z₁ Z₂ k :
  (complex p δ Z₁ Z₂ k).f = AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k))

/- Compatibility check for the second arrow of the closed-cover short complex. -/
#check (complex_g p δ Z₁ Z₂ k :
  (complex p δ Z₁ Z₂ k).g = AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k))

/- Compatibility check for exactness and right surjectivity of the closed-cover complex. -/
#check (exact p δ Z₁ Z₂ :
  Z₁.support ⊔ Z₂.support = ⊤ →
    ∀ k : ℤ, (complex p δ Z₁ Z₂ k).Exact ∧ Epi (complex p δ Z₁ Z₂ k).g)

end AlgebraicGeometry.CycleGroup.ClosedCover
