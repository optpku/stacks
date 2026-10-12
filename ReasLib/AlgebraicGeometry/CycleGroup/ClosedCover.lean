/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.ClosedCover

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]

/-- Pushforward from the scheme-theoretic intersection to the two closed subschemes,
with a negative sign in the second component. -/
noncomputable def intersectionMap (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    CycleGroup (Scheme.schemeTheoreticIntersection Z₁ Z₂)
        (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) k →+
      CycleGroup Z₁.subscheme
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k ×
        CycleGroup Z₂.subscheme
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k :=
  (CycleGroup.mapHom
      (Scheme.IdealSheafData.inclusion (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂))
      (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ)
      ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k).prod
    (-CycleGroup.mapHom
      (Scheme.IdealSheafData.inclusion (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂))
      (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ)
      ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k)

/-- The intersection map sends a cycle to the pair of inclusion pushforwards, with the
second pushforward negated. -/
theorem intersectionMap_apply (Z₁ Z₂ : X.IdealSheafData) (k : ℤ)
    (c : CycleGroup (Scheme.schemeTheoreticIntersection Z₁ Z₂)
      (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) k) :
    intersectionMap p δ Z₁ Z₂ k c =
      (CycleGroup.mapHom
          (Scheme.IdealSheafData.inclusion (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂))
          (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ)
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k c,
        -CycleGroup.mapHom
          (Scheme.IdealSheafData.inclusion (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂))
          (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ)
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k c) := sorry

/-- The sum of pushforwards from the two closed subschemes to the ambient scheme. -/
noncomputable def coverMap (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    (CycleGroup Z₁.subscheme
        ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k ×
      CycleGroup Z₂.subscheme
        ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k) →+
      CycleGroup X (p.relativeDimensionFunction δ) k :=
  (CycleGroup.mapHom Z₁.subschemeι
      ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ)
      (p.relativeDimensionFunction δ) k).coprod
    (CycleGroup.mapHom Z₂.subschemeι
      ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ)
      (p.relativeDimensionFunction δ) k)

/-- The cover map sends a pair of cycles to the sum of their ambient pushforwards. -/
theorem coverMap_apply (Z₁ Z₂ : X.IdealSheafData) (k : ℤ)
    (c : CycleGroup Z₁.subscheme
        ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k ×
      CycleGroup Z₂.subscheme
        ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k) :
    coverMap p δ Z₁ Z₂ k c =
      CycleGroup.mapHom Z₁.subschemeι
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ)
          (p.relativeDimensionFunction δ) k c.1 +
        CycleGroup.mapHom Z₂.subschemeι
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ)
          (p.relativeDimensionFunction δ) k c.2 := sorry

/-- The intersection pushforward followed by the sum of ambient pushforwards is zero. -/
theorem intersectionMap_comp_coverMap (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k) ≫
      AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k) = 0 := sorry

/-- The short complex of degree-`k` cycle groups associated to two closed subschemes. -/
noncomputable def complex (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k))
    (AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k))
    (intersectionMap_comp_coverMap p δ Z₁ Z₂ k)

/-- The first arrow in the closed-cover complex is the signed intersection pushforward. -/
theorem complex_f (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    (complex p δ Z₁ Z₂ k).f = AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k) := sorry

/-- The second arrow in the closed-cover complex is the sum of the two ambient pushforwards. -/
theorem complex_g (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    (complex p δ Z₁ Z₂ k).g = AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k) := sorry

/-- For two closed subschemes whose supports cover the ambient scheme, the associated
cycle-group complex is exact at its middle term and its second arrow is an epimorphism. -/
theorem exact {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (Z₁ Z₂ : X.IdealSheafData) (hcover : Z₁.support ⊔ Z₂.support = ⊤) (k : ℤ) :
    (complex p δ Z₁ Z₂ k).Exact ∧ Epi (complex p δ Z₁ Z₂ k).g := sorry

end AlgebraicGeometry.CycleGroup.ClosedCover
