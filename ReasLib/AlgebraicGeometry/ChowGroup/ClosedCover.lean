/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.ClosedCover
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

/-!
# Chow groups of a closed cover

This file defines the signed pushforward complex on Chow groups associated to a cover by
two closed subschemes and states its exactness.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ClosedCover

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The first intersection inclusion commutes with the structure morphisms to `S`. -/
theorem firstInclusion_comp (Z₁ Z₂ : X.IdealSheafData) :
    Scheme.IdealSheafData.inclusion (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂) ≫
        (Z₁.subschemeι ≫ p) =
      (Z₁ ⊔ Z₂).subschemeι ≫ p := sorry

/-- The second intersection inclusion commutes with the structure morphisms to `S`. -/
theorem secondInclusion_comp (Z₁ Z₂ : X.IdealSheafData) :
    Scheme.IdealSheafData.inclusion (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂) ≫
        (Z₂.subschemeι ≫ p) =
      (Z₁ ⊔ Z₂).subschemeι ≫ p := sorry

/-- Pushforward from the scheme-theoretic intersection to the two closed subschemes,
with a negative sign in the second component. -/
noncomputable def intersectionMap (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    @ChowGroup (Scheme.schemeTheoreticIntersection Z₁ Z₂)
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) (Z₁ ⊔ Z₂))
        (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup Z₁.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) Z₁)
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k ×
        @ChowGroup Z₂.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) Z₂)
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k :=
  let i₁ : (Z₁ ⊔ Z₂).subscheme ⟶ Z₁.subscheme :=
    Scheme.IdealSheafData.inclusion (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂)
  let i₂ : (Z₁ ⊔ Z₂).subscheme ⟶ Z₂.subscheme :=
    Scheme.IdealSheafData.inclusion (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂)
  let f₁ : Over.mk ((Z₁ ⊔ Z₂).subschemeι ≫ p) ⟶ Over.mk (Z₁.subschemeι ≫ p) :=
    Over.homMk i₁ (firstInclusion_comp p Z₁ Z₂)
  let f₂ : Over.mk ((Z₁ ⊔ Z₂).subschemeι ≫ p) ⟶ Over.mk (Z₂.subschemeι ≫ p) :=
    Over.homMk i₂ (secondInclusion_comp p Z₁ Z₂)
  let hi₁ : IsProper (Scheme.IdealSheafData.inclusion
      (le_sup_left : Z₁ ≤ Z₁ ⊔ Z₂) : (Z₁ ⊔ Z₂).subscheme ⟶ Z₁.subscheme) := inferInstance
  let hi₂ : IsProper (Scheme.IdealSheafData.inclusion
      (le_sup_right : Z₂ ≤ Z₁ ⊔ Z₂) : (Z₁ ⊔ Z₂).subscheme ⟶ Z₂.subscheme) := inferInstance
  let h₁ : IsProper f₁.left :=
    @AlgebraicGeometry.instIsProperOverHomMk (Z₁ ⊔ Z₂).subscheme Z₁.subscheme
      i₁ hi₁ S (Z₁.subschemeι ≫ p)
  let h₂ : IsProper f₂.left :=
    @AlgebraicGeometry.instIsProperOverHomMk (Z₁ ⊔ Z₂).subscheme Z₂.subscheme
      i₂ hi₂ S (Z₂.subschemeι ≫ p)
  (@ChowGroup.map S inferInstance δ inferInstance
      (Over.mk ((Z₁ ⊔ Z₂).subschemeι ≫ p)) (Over.mk (Z₁.subschemeι ≫ p))
      inferInstance inferInstance f₁ h₁ k).prod
    (-@ChowGroup.map S inferInstance δ inferInstance
      (Over.mk ((Z₁ ⊔ Z₂).subschemeι ≫ p)) (Over.mk (Z₂.subschemeι ≫ p))
      inferInstance inferInstance f₂ h₂ k)

/-- The signed intersection map on a cycle class is induced by the corresponding cycle map. -/
theorem intersectionMap_chowClass (Z₁ Z₂ : X.IdealSheafData) (k : ℤ)
    (c : CycleGroup (Scheme.schemeTheoreticIntersection Z₁ Z₂)
      (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) k) :
    intersectionMap p δ Z₁ Z₂ k
        (@chowClass (Scheme.schemeTheoreticIntersection Z₁ Z₂)
          (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) (Z₁ ⊔ Z₂))
          (((Z₁ ⊔ Z₂).subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k c) =
      (@chowClass Z₁.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) Z₁)
          ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k
          (CycleGroup.ClosedCover.intersectionMap p δ Z₁ Z₂ k c).1,
        @chowClass Z₂.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) Z₂)
          ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k
          (CycleGroup.ClosedCover.intersectionMap p δ Z₁ Z₂ k c).2) := sorry

/-- The sum of pushforwards from the two closed subschemes to the ambient scheme. -/
noncomputable def coverMap (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    (@ChowGroup Z₁.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p) Z₁)
        ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k ×
      @ChowGroup Z₂.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p) Z₂)
        ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k) →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  let f₁ : Over.mk (Z₁.subschemeι ≫ p) ⟶ Over.mk p :=
    Over.homMk (Z₁.subschemeι : Z₁.subscheme ⟶ X) rfl
  let f₂ : Over.mk (Z₂.subschemeι ≫ p) ⟶ Over.mk p :=
    Over.homMk (Z₂.subschemeι : Z₂.subscheme ⟶ X) rfl
  let hi₁ : IsProper (Z₁.subschemeι : Z₁.subscheme ⟶ X) := inferInstance
  let hi₂ : IsProper (Z₂.subschemeι : Z₂.subscheme ⟶ X) := inferInstance
  let h₁ : IsProper f₁.left :=
    @AlgebraicGeometry.instIsProperOverHomMk Z₁.subscheme X Z₁.subschemeι hi₁ S p
  let h₂ : IsProper f₂.left :=
    @AlgebraicGeometry.instIsProperOverHomMk Z₂.subscheme X Z₂.subschemeι hi₂ S p
  (@ChowGroup.map S inferInstance δ inferInstance (Over.mk (Z₁.subschemeι ≫ p))
      (Over.mk p) inferInstance inferInstance f₁ h₁ k).coprod
    (@ChowGroup.map S inferInstance δ inferInstance (Over.mk (Z₂.subschemeι ≫ p))
      (Over.mk p) inferInstance inferInstance f₂ h₂ k)

/-- The cover map on cycle classes is induced by the sum of the ambient cycle pushforwards. -/
theorem coverMap_chowClass (Z₁ Z₂ : X.IdealSheafData) (k : ℤ)
    (c₁ : CycleGroup Z₁.subscheme
      ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) k)
    (c₂ : CycleGroup Z₂.subscheme
      ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) k) :
    coverMap p δ Z₁ Z₂ k
        (@chowClass Z₁.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) Z₁)
            ((Z₁.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k c₁,
          @chowClass Z₂.subscheme (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) Z₂)
            ((Z₂.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k c₂) =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k
        (CycleGroup.ClosedCover.coverMap p δ Z₁ Z₂ k (c₁, c₂)) := sorry

/-- The intersection pushforward followed by the sum of ambient pushforwards is zero. -/
theorem intersectionMap_comp_coverMap (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k) ≫
      AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k) = 0 := sorry

/-- The short complex of degree-`k` Chow groups associated to two closed subschemes. -/
noncomputable def complex (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k))
    (AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k))
    (intersectionMap_comp_coverMap p δ Z₁ Z₂ k)

/-- The first arrow in the Chow closed-cover complex is the signed intersection pushforward. -/
theorem complex_f (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    (complex p δ Z₁ Z₂ k).f =
      AddCommGrpCat.ofHom (intersectionMap p δ Z₁ Z₂ k) := sorry

/-- The second arrow in the Chow closed-cover complex is the sum of ambient pushforwards. -/
theorem complex_g (Z₁ Z₂ : X.IdealSheafData) (k : ℤ) :
    (complex p δ Z₁ Z₂ k).g = AddCommGrpCat.ofHom (coverMap p δ Z₁ Z₂ k) := sorry

/-- For two closed subschemes whose supports cover the ambient scheme, the associated
Chow-group complex is exact at its middle term and its second arrow is an epimorphism. -/
theorem exact {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (Z₁ Z₂ : X.IdealSheafData) (hcover : Z₁.support ⊔ Z₂.support = ⊤) (k : ℤ) :
    (complex p δ Z₁ Z₂ k).Exact ∧ Epi (complex p δ Z₁ Z₂ k).g := sorry

end AlgebraicGeometry.ChowGroup.ClosedCover
