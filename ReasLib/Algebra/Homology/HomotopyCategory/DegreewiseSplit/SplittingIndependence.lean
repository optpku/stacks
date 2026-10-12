/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.CochainHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Independence of degreewise splitting choices

The triangle attached to a termwise split short complex is canonical up to the identity on its
three vertices.  This leaf keeps the selected correction family and the connecting-map homotopy
available as separate API, then packages the resulting triangle isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated ComplexShape HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex (CochainComplex C ℤ))
variable (σ σ' : ∀ n : ℤ, (S.map (eval C (up ℤ) n)).Splitting)

namespace DegreewiseSplit.Splitting

/-- The canonical family of section corrections from `σ` to `σ'`. -/
@[stacks 05SS "canonical correction between degreewise splittings"]
def correction :
    ∀ n : ℤ, (S.map (eval C (up ℤ) n)).X₃ ⟶ (S.map (eval C (up ℤ) n)).X₁ :=
  fun n ↦ (σ' n).s ≫ (σ n).r

/-- The canonical correction changes the chosen section from `σ` to `σ'`. -/
@[stacks 05SS "section correction specification"]
theorem correction_spec :
    ∀ n : ℤ,
      (σ n).IsSectionCorrection (σ' n) (correction S σ σ' n) := sorry

/-- Changing the degreewise splitting changes the connecting cochain map by a homotopy. -/
@[stacks 05SS "homotopy of connecting maps under splitting change"]
noncomputable def homotopy :
    Homotopy (homOfDegreewiseSplit S σ') (homOfDegreewiseSplit S σ) :=
  DegreewiseSplit.Homotopy.ofCorrection S σ σ'
    (correction S σ σ')
    (correction_spec S σ σ')

/-- The two connecting maps define the same morphism in the homotopy category. -/
@[stacks 05SS "connecting-map splitting independence in the homotopy category"]
theorem eq_in_homotopyCategory :
    (HomotopyCategory.quotient C (up ℤ)).map (homOfDegreewiseSplit S σ') =
      (HomotopyCategory.quotient C (up ℤ)).map (homOfDegreewiseSplit S σ) := sorry

namespace TriangleIso

/-- The first square of the identity comparison between the two splitting triangles commutes. -/
theorem comm₁ :
    (trianglehOfDegreewiseSplit S σ).mor₁ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (trianglehOfDegreewiseSplit S σ').mor₁ := sorry

/-- The second square of the identity comparison between the two splitting triangles commutes. -/
theorem comm₂ :
    (trianglehOfDegreewiseSplit S σ).mor₂ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (trianglehOfDegreewiseSplit S σ').mor₂ := sorry

/-- The third square of the identity comparison between the two splitting triangles commutes. -/
theorem comm₃ :
    (trianglehOfDegreewiseSplit S σ).mor₃ ≫ (Iso.refl _).hom⟦(1 : ℤ)⟧' =
      (Iso.refl _).hom ≫ (trianglehOfDegreewiseSplit S σ').mor₃ := sorry

end TriangleIso

/-- Lemma 22.8.1 (09K6): the triangles attached to two degreewise splittings are canonically
isomorphic by identity maps on all three vertices. -/
@[stacks 05SS "triangle independence of the degreewise splitting",
  stacks 09K6 "triangle independence for an admissible short exact sequence"]
noncomputable def triangleIso :
    trianglehOfDegreewiseSplit S σ ≅ trianglehOfDegreewiseSplit S σ' :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (TriangleIso.comm₁ S σ σ') (TriangleIso.comm₂ S σ σ') (TriangleIso.comm₃ S σ σ')

/-- The canonical splitting-independence isomorphism is the identity on the first vertex. -/
@[simp]
theorem triangleIso_hom_hom₁ :
    (triangleIso S σ σ').hom.hom₁ = 𝟙 _ := sorry

/-- The canonical splitting-independence isomorphism is the identity on the second vertex. -/
@[simp]
theorem triangleIso_hom_hom₂ :
    (triangleIso S σ σ').hom.hom₂ = 𝟙 _ := sorry

/-- The canonical splitting-independence isomorphism is the identity on the third vertex. -/
@[simp]
theorem triangleIso_hom_hom₃ :
    (triangleIso S σ σ').hom.hom₃ = 𝟙 _ := sorry

end DegreewiseSplit.Splitting

end CochainComplex
