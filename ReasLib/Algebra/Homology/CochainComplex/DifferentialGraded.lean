/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import ReasLib.Algebra.Category.DifferentialGraded

/-!
# Differential Graded Category of Cochain Complexes

For every preadditive category, its `ℤ`-indexed cochain complexes form a
differential graded category over `ℤ`; more generally, a chosen commutative
linear base ring gives an explicit differential graded category model.  This
file owns those enrichment models.  The separate functor leaf packages the
action of additive functors on the canonical integral model.
-/

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

noncomputable section

universe u v w

namespace CategoryTheory.CochainComplex

variable (𝒝 : Type u) [Category.{v} 𝒝] [Preadditive 𝒝]

private theorem cochain_comp_castHom {A B C : CochainComplex 𝒝 ℤ}
    {i j k l : ℤ} (f : Cochain A B i) (g : Cochain B C j)
    (h : i + j = k) (e : k = l) :
    @castHom ℤ (fun n : ℤ ↦ Cochain A C n) k l e (Cochain.comp f g h) =
      Cochain.comp f g (h.trans e) := by
  cases e
  rfl

/-- The Hom-complex differential squares to zero. -/
theorem complexesDgDifferential_sq {A B : CochainComplex 𝒝 ℤ}
    (n : ℤ) (f : Cochain A B n) :
    δ (n + 1) (n + 1 + 1) (δ n (n + 1) f) = 0 := by
  exact δ_δ n (n + 1) (n + 1 + 1) f

/-- The identity cochain is closed for the Hom-complex differential. -/
theorem complexesDgId_closed (A : CochainComplex 𝒝 ℤ) :
    δ 0 1 ((((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0) : Cochain A A 0)) = 0 := by
  exact δ_ofHom (𝟙 A)

/-- Left unit for homogeneous composition of cochains. -/
theorem complexesDgComp_id_left {A B : CochainComplex 𝒝 ℤ}
    {n : ℤ} (f : Cochain A B n) :
    castHom (add_zero n) (Cochain.comp f (((Cocycle.equivHom B B) (𝟙 B) : Cocycle B B 0)) rfl) =
      f := by
  rw [cochain_comp_castHom]
  exact Cochain.comp_id f

/-- Right unit for homogeneous composition of cochains. -/
theorem complexesDgComp_id_right {A B : CochainComplex 𝒝 ℤ}
    {n : ℤ} (f : Cochain A B n) :
    castHom (zero_add n) (Cochain.comp (((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0)) f rfl) =
      f := by
  rw [cochain_comp_castHom]
  exact Cochain.id_comp f

/-- Associativity of homogeneous composition of cochains. -/
theorem complexesDgComp_assoc {W X Y Z : CochainComplex 𝒝 ℤ}
    {i j k : ℤ}
    (h : Cochain Y Z k) (g : Cochain X Y j) (f : Cochain W X i) :
    castHom (add_assoc i j k) (Cochain.comp (Cochain.comp f g rfl) h rfl) =
      Cochain.comp f (Cochain.comp g h rfl) rfl := by
  rw [cochain_comp_castHom]
  exact Cochain.comp_assoc f g h rfl rfl (add_assoc i j k)

/-- Homogeneous composition is additive in its left input. -/
theorem complexesDgComp_add_left {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (g₁ g₂ : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp f (g₁ + g₂) rfl = Cochain.comp f g₁ rfl + Cochain.comp f g₂ rfl := by
  exact Cochain.comp_add f g₁ g₂ rfl

/-- Homogeneous composition is additive in its right input. -/
theorem complexesDgComp_add_right {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (g : Cochain B C j) (f₁ f₂ : Cochain A B i) :
    Cochain.comp (f₁ + f₂) g rfl = Cochain.comp f₁ g rfl + Cochain.comp f₂ g rfl := by
  exact Cochain.add_comp f₁ f₂ g rfl

/-- Homogeneous composition is `ℤ`-linear in its left input. -/
theorem complexesDgComp_zsmul_left {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (r : ℤ) (g : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp f (r • g) rfl = r • Cochain.comp f g rfl := by
  exact Cochain.comp_smul f r g rfl

/-- Homogeneous composition is `ℤ`-linear in its right input. -/
theorem complexesDgComp_zsmul_right {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (r : ℤ) (g : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp (r • f) g rfl = r • Cochain.comp f g rfl := by
  exact Cochain.smul_comp r f g rfl

/-- The Hom-complex differential is additive. -/
theorem complexesDgDifferential_add {A B : CochainComplex 𝒝 ℤ}
    (n : ℤ) (f g : Cochain A B n) :
    δ n (n + 1) (f + g) = δ n (n + 1) f + δ n (n + 1) g := by
  exact δ_add n (n + 1) f g

/-- The Hom-complex differential is `ℤ`-linear. -/
theorem complexesDgDifferential_zsmul {A B : CochainComplex 𝒝 ℤ}
    (n r : ℤ) (f : Cochain A B n) :
    δ n (n + 1) (r • f) = r • δ n (n + 1) f := by
  exact δ_smul n (n + 1) r f

/-- The Hom-complex differential satisfies the graded Leibniz rule on homogeneous cochains. -/
theorem complexesDgDifferential_comp {A B C : CochainComplex 𝒝 ℤ}
    {i j : ℤ} (g : Cochain B C j) (f : Cochain A B i) :
    δ (i + j) (i + j + 1) (Cochain.comp f g rfl) =
      @castHom ℤ (fun n : ℤ ↦ Cochain A C n) _ _ (d_comp_left_index i j)
          (Cochain.comp f (δ j (j + 1) g) rfl) +
        (j.negOnePow : ℤ) •
          @castHom ℤ (fun n : ℤ ↦ Cochain A C n) _ _ (d_comp_right_index i j)
            (Cochain.comp (δ i (i + 1) f) g rfl) := by
  rw [cochain_comp_castHom, cochain_comp_castHom]
  exact δ_comp f g rfl (i + 1) (j + 1) (i + j + 1) rfl rfl rfl

/-- Homogeneous cochain composition is linear in its left input over a chosen linear base ring.
-/
theorem cochainComplexDgComp_smul_left
    {R : Type w} [CommRing R] [Linear R 𝒝]
    {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (r : R) (g : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp f (r • g) rfl = r • Cochain.comp f g rfl := by
  exact Cochain.comp_smul f r g rfl

/-- Homogeneous cochain composition is linear in its right input over a chosen linear base ring.
-/
theorem cochainComplexDgComp_smul_right
    {R : Type w} [CommRing R] [Linear R 𝒝]
    {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (r : R) (g : Cochain B C j) (f : Cochain A B i) :
    Cochain.comp (r • f) g rfl = r • Cochain.comp f g rfl := by
  exact Cochain.smul_comp r f g rfl

/-- The Hom-complex differential is linear over a chosen linear base ring. -/
theorem cochainComplexDgDifferential_smul
    {R : Type w} [CommRing R] [Linear R 𝒝]
    {A B : CochainComplex 𝒝 ℤ}
    (n : ℤ) (r : R) (f : Cochain A B n) :
    δ n (n + 1) (r • f) = r • δ n (n + 1) f := by
  exact δ_smul n (n + 1) r f

/-- The Hom-complex differential satisfies the graded Leibniz rule over a chosen linear base
ring. -/
theorem cochainComplexDgDifferential_comp
    {R : Type w} [CommRing R] [Linear R 𝒝]
    {A B C : CochainComplex 𝒝 ℤ}
    {i j : ℤ} (g : Cochain B C j) (f : Cochain A B i) :
    δ (i + j) (i + j + 1) (Cochain.comp f g rfl) =
      @castHom ℤ (fun n : ℤ ↦ Cochain A C n) _ _ (d_comp_left_index i j)
          (Cochain.comp f (δ j (j + 1) g) rfl) +
        (j.negOnePow : R) •
          @castHom ℤ (fun n : ℤ ↦ Cochain A C n) _ _ (d_comp_right_index i j)
            (Cochain.comp (δ i (i + 1) f) g rfl) := by
  simpa only [Int.cast_smul_eq_zsmul] using (complexesDgDifferential_comp 𝒝 g f)

/-- The differential graded category of cochain complexes over a chosen commutative base ring
acting linearly on the ambient preadditive category.  The base ring is explicit because a single
category can carry more than one linear structure. -/
@[reducible]
noncomputable def differentialGradedCategory
    (R : Type w) [CommRing R] [Linear R 𝒝] :
    DifferentialGradedCategory R (CochainComplex 𝒝 ℤ) where
  Hom := fun A B n ↦ Cochain A B n
  homAddCommGroup := fun _ _ _ ↦ inferInstance
  homModule := fun _ _ _ ↦ inferInstance
  d := fun n f ↦ δ n (n + 1) f
  id := fun A ↦ ((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0)
  comp := fun g f ↦ Cochain.comp f g rfl
  d_sq := fun n f ↦ complexesDgDifferential_sq 𝒝 n f
  d_id := fun A ↦ complexesDgId_closed 𝒝 A
  id_comp_hom := fun f ↦ complexesDgComp_id_left 𝒝 f
  comp_id_hom := fun f ↦ complexesDgComp_id_right 𝒝 f
  comp_assoc := fun h g f ↦ complexesDgComp_assoc 𝒝 h g f
  comp_add_left := fun g₁ g₂ f ↦ complexesDgComp_add_left 𝒝 g₁ g₂ f
  comp_add_right := fun g f₁ f₂ ↦ complexesDgComp_add_right 𝒝 g f₁ f₂
  comp_smul_left := fun r g f ↦ cochainComplexDgComp_smul_left 𝒝 r g f
  comp_smul_right := fun r g f ↦ cochainComplexDgComp_smul_right 𝒝 r g f
  d_add := fun n f g ↦ complexesDgDifferential_add 𝒝 n f g
  d_smul := fun n r f ↦ cochainComplexDgDifferential_smul 𝒝 n r f
  d_comp := fun g f ↦ cochainComplexDgDifferential_comp 𝒝 g f

/-- The graded Hom object of the explicit `R`-linear cochain-complex DG category is the
corresponding group of homogeneous cochains. -/
@[simp]
theorem differentialGradedCategory_hom
    (R : Type w) [CommRing R] [Linear R 𝒝]
    (A B : CochainComplex 𝒝 ℤ) (n : ℤ) :
    (differentialGradedCategory 𝒝 R).Hom A B n = Cochain A B n := by
  rfl

/-- The differential in the explicit `R`-linear cochain-complex DG category is the Hom-complex
differential. -/
@[simp]
theorem differentialGradedCategory_d
    (R : Type w) [CommRing R] [Linear R 𝒝]
    {A B : CochainComplex 𝒝 ℤ} (n : ℤ) (f : Cochain A B n) :
    (differentialGradedCategory 𝒝 R).d n f = δ n (n + 1) f := by
  rfl

/-- The identity of the explicit `R`-linear cochain-complex DG category is the degree-zero
cocycle associated to the identity map of complexes. -/
@[simp]
theorem differentialGradedCategory_id
    (R : Type w) [CommRing R] [Linear R 𝒝]
    (A : CochainComplex 𝒝 ℤ) :
    (differentialGradedCategory 𝒝 R).id A =
      (((Cocycle.equivHom A A) (𝟙 A) : Cocycle A A 0) : Cochain A A 0) := by
  rfl

/-- Composition in the explicit `R`-linear cochain-complex DG category is homogeneous cochain
composition. -/
@[simp]
theorem differentialGradedCategory_comp
    (R : Type w) [CommRing R] [Linear R 𝒝]
    {A B C : CochainComplex 𝒝 ℤ} {i j : ℤ}
    (g : Cochain B C j) (f : Cochain A B i) :
    (differentialGradedCategory 𝒝 R).comp g f = Cochain.comp f g rfl := by
  rfl

/-- The cochain complexes in a preadditive category form the canonical differential graded
category over `ℤ`, with the Hom
complex as its graded Hom object. -/
@[stacks 09L9, reducible]
instance complexesDifferentialGradedCategory :
    DifferentialGradedCategory ℤ (CochainComplex 𝒝 ℤ) :=
  differentialGradedCategory 𝒝 ℤ

/-- The graded Hom object of the cochain-complex DG category is the corresponding group of
homogeneous cochains. -/
@[simp]
theorem complexesDifferentialGradedCategory_hom
    (A B : CochainComplex 𝒝 ℤ) (n : ℤ) :
    (A ⟶[n] B) = Cochain A B n := by
  rfl

end CategoryTheory.CochainComplex
