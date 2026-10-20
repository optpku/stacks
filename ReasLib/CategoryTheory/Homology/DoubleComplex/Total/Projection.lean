module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Summand Projections on Total Complexes

This leaf provides the morphism from a total-complex degree to one chosen bidegree summand.  It is
dual in purpose to Mathlib's `ιTotal`, while remaining independent of a particular filtration,
coordinate convention, or spectral-sequence construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v w₁ w₂ w

namespace HomologicalComplex₂

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c] [DecidableEq I]
variable (K : HomologicalComplex₂ C c₁ c₂) [K.HasTotal c]

namespace Total

/-- The projection from total degree `n` to the bidegree `(i₁, i₂)` summand.

When `(i₁, i₂)` does not lie over `n`, this is the zero projection. -/
@[stacks 0130 "total-complex summand projection"]
noncomputable def πTotal (i₁ : I₁) (i₂ : I₂) (n : I) :
    (K.total c).X n ⟶ (K.X i₁).X i₂ :=
  K.totalDesc fun j₁ j₂ _ ↦
    @dite _ (j₁ = i₁) (Classical.propDecidable _) (fun h₁ ↦
      @dite _ (j₂ = i₂) (Classical.propDecidable _) (fun h₂ ↦
        (K.XXIsoOfEq _ _ _ h₁ h₂).hom) (fun _ ↦ 0)) (fun _ ↦ 0)

/-- Composing a total-complex summand inclusion with `πTotal` selects the matching summand. -/
@[stacks 0130 "total-complex summand projection computation", reassoc (attr := simp)]
theorem ιTotal_πTotal (i₁ : I₁) (i₂ : I₂) (j₁ : I₁) (j₂ : I₂) (n : I)
    (hj : ComplexShape.π c₁ c₂ c (j₁, j₂) = n) :
    K.ιTotal c j₁ j₂ n hj ≫ Total.πTotal K i₁ i₂ n =
      @dite _ (j₁ = i₁) (Classical.propDecidable _) (fun h₁ ↦
        @dite _ (j₂ = i₂) (Classical.propDecidable _) (fun h₂ ↦
          (K.XXIsoOfEq _ _ _ h₁ h₂).hom) (fun _ ↦ 0)) (fun _ ↦ 0) := sorry

/-- A projection vanishes on a summand whose first index does not match. -/
@[stacks 0130 "total-complex projection off the first index", reassoc (attr := simp)]
theorem ιTotal_πTotal_of_ne_left
    (i₁ : I₁) (i₂ : I₂) (j₁ : I₁) (j₂ : I₂) (n : I)
    (hj : ComplexShape.π c₁ c₂ c (j₁, j₂) = n) (hij : j₁ ≠ i₁) :
    K.ιTotal c j₁ j₂ n hj ≫ Total.πTotal K i₁ i₂ n = 0 := sorry

/-- A projection vanishes on a summand whose second index does not match. -/
@[stacks 0130 "total-complex projection off the second index", reassoc (attr := simp)]
theorem ιTotal_πTotal_of_ne_right
    (i₁ : I₁) (i₂ : I₂) (j₁ : I₁) (j₂ : I₂) (n : I)
    (hj : ComplexShape.π c₁ c₂ c (j₁, j₂) = n) (hij : j₂ ≠ i₂) :
    K.ιTotal c j₁ j₂ n hj ≫ Total.πTotal K i₁ i₂ n = 0 := sorry

/-- The inclusion and projection of one total-complex summand compose to its identity. -/
@[stacks 0130 "total-complex summand projection identity", reassoc (attr := simp)]
theorem ιTotal_πTotal_self (i₁ : I₁) (i₂ : I₂) (n : I)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = n) :
    K.ιTotal c i₁ i₂ n h ≫ Total.πTotal K i₁ i₂ n = 𝟙 _ := sorry

end Total

end

end HomologicalComplex₂
