/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Admissible.Decomposition
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Orthogonals of Admissible Subcategories

Adjointability identifies a subcategory, or its strict-full closure, with a
double orthogonal.  Retract closure is then exposed as a consequence of the
canonical orthogonal owner.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty.Admissible

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (A : ObjectProperty D) [A.IsTriangulated]

namespace Right

/-- Stacks 0CQS: if the inclusion of `A` has a right adjoint, the strict-full
closure of `A` is the left orthogonal of `A.rightOrthogonal`. -/
@[stacks 0CQS]
theorem isoClosure_eq (hA : A.ι.IsLeftAdjoint) :
    A.isoClosure = A.rightOrthogonal.leftOrthogonal := by
  apply le_antisymm
  · rintro X ⟨Y, hY, ⟨e⟩⟩ Z f hZ
    rw [← cancel_epi e.inv, comp_zero]
    exact hZ _ hY
  · intro X hX
    obtain ⟨R, ⟨adj⟩⟩ := hA.exists_rightAdjoint
    let c : A.ι.obj (R.obj X) ⟶ X := adj.counit.app X
    have hbij (Y : D) (hY : A Y) :
        Function.Bijective (fun f : Y ⟶ A.ι.obj (R.obj X) ↦ f ≫ c) :=
      ((A.fullyFaithfulι.homEquiv (X := ⟨Y, hY⟩) (Y := R.obj X)).symm.trans
        (adj.homEquiv ⟨Y, hY⟩ X).symm).bijective
    obtain ⟨B, g, h, hT⟩ := distinguished_cocone_triangle c
    let T := Triangle.mk c g h
    have hcg : c ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT
    have hhc : h ≫ c⟦1⟧' = 0 := comp_distTriang_mor_zero₃₁ T hT
    -- Exactness and stability under inverse shifts make the cone right orthogonal.
    have hB : A.rightOrthogonal B := by
      intro Y f hY
      let s : shiftFunctor D (-1 : ℤ) ⊣ shiftFunctor D (1 : ℤ) :=
        (shiftEquiv D (1 : ℤ)).symm.toAdjunction
      have hs₀ (Z : D) : s.homEquiv Y Z 0 = 0 := by
        change s.unit.app Y ≫ (shiftFunctor D (1 : ℤ)).map
          (0 : Y⟦(-1 : ℤ)⟧ ⟶ Z) = 0
        rw [Functor.map_zero]
        exact comp_zero
      obtain ⟨a, ha⟩ := (s.homEquiv Y (A.ι.obj (R.obj X))).surjective (f ≫ h)
      have ha₀ : a ≫ c = 0 := by
        apply (s.homEquiv Y X).injective
        calc
          s.homEquiv Y X (a ≫ c) = s.homEquiv Y _ a ≫ c⟦1⟧' :=
            s.homEquiv_naturality_right a c
          _ = (f ≫ h) ≫ c⟦1⟧' := by rw [ha]
          _ = 0 := by rw [Category.assoc, hhc, comp_zero]
          _ = s.homEquiv Y X 0 := (hs₀ X).symm
      have ha' : a = 0 := (hbij _ (A.le_shift (-1) _ hY)).injective (by
        simpa only [zero_comp] using ha₀)
      have hf : f ≫ h = 0 := by
        rw [← ha, ha']
        exact hs₀ _
      obtain ⟨b, hb⟩ : ∃ b : Y ⟶ X, f = b ≫ g :=
        Triangle.coyoneda_exact₃ T hT f hf
      obtain ⟨a, ha⟩ := (hbij Y hY).surjective b
      change a ≫ c = b at ha
      rw [hb, ← ha, Category.assoc, hcg, comp_zero]
    -- In the double orthogonal, this cone vanishes and the counit is an isomorphism.
    have hg : g = 0 := hX g hB
    obtain ⟨b, hb⟩ : ∃ b : (A.ι.obj (R.obj X))⟦(1 : ℤ)⟧ ⟶ B, 𝟙 B = h ≫ b :=
      Triangle.yoneda_exact₂ T.rotate (rot_of_distTriang T hT)
        (𝟙 B) (by
          change g ≫ 𝟙 B = 0
          simpa using hg)
    have hB₀ : IsZero B := by
      apply (IsZero.iff_id_eq_zero B).2
      rw [hb, hB b (A.le_shift 1 _ (R.obj X).property), comp_zero]
    haveI : IsIso c := (Triangle.isZero₃_iff_isIso₁ T hT).1 hB₀
    exact ⟨A.ι.obj (R.obj X), (R.obj X).property, ⟨(asIso c).symm⟩⟩

/-- Stacks 0CQS: right adjointability makes the strict-full closure of `A`
stable under retracts. -/
@[stacks 0CQS]
theorem isoClosure_closedUnderRetracts (hA : A.ι.IsLeftAdjoint) :
    A.isoClosure.IsStableUnderRetracts := by
  rw [isoClosure_eq A hA]
  constructor
  intro X Y r hY Z f hZ
  calc
    f = r.i ≫ (r.r ≫ f) := by simp
    _ = 0 := by rw [hY (r.r ≫ f) hZ, comp_zero]

/-- Stacks 0CQS: a strictly full right-adjointable subcategory is the left
orthogonal of its right orthogonal. -/
@[stacks 0CQS]
theorem eq_leftOrthogonal [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsLeftAdjoint) :
    A = A.rightOrthogonal.leftOrthogonal := by
  simpa only [A.isoClosure_eq_self] using isoClosure_eq A hA

/-- Stacks 0CQS: a strictly full right-adjointable subcategory is stable under
retracts. -/
@[stacks 0CQS]
theorem closedUnderRetracts [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsLeftAdjoint) :
    A.IsStableUnderRetracts := by
  simpa only [A.isoClosure_eq_self] using isoClosure_closedUnderRetracts A hA

end Right

namespace Left

/-- Stacks 0CQT: if the inclusion of `A` has a left adjoint, the strict-full
closure of `A` is the right orthogonal of `A.leftOrthogonal`. -/
@[stacks 0CQT]
theorem isoClosure_eq (hA : A.ι.IsRightAdjoint) :
    A.isoClosure = A.leftOrthogonal.rightOrthogonal := by
  apply le_antisymm
  · rintro X ⟨Y, hY, ⟨e⟩⟩ Z f hZ
    rw [← cancel_mono e.hom, zero_comp]
    exact hZ _ hY
  · intro X hX
    obtain ⟨L, ⟨adj⟩⟩ := hA.exists_leftAdjoint
    let c : X ⟶ A.ι.obj (L.obj X) := adj.unit.app X
    have hbij (Y : D) (hY : A Y) :
        Function.Bijective (fun f : A.ι.obj (L.obj X) ⟶ Y ↦ c ≫ f) :=
      ((A.fullyFaithfulι.homEquiv (X := L.obj X) (Y := ⟨Y, hY⟩)).symm.trans
        (adj.homEquiv X ⟨Y, hY⟩)).bijective
    obtain ⟨B, g, h, hT⟩ := distinguished_cocone_triangle c
    let T := Triangle.mk c g h
    have hcg : c ≫ g = 0 := comp_distTriang_mor_zero₁₂ T hT
    have hhc : h ≫ c⟦1⟧' = 0 := comp_distTriang_mor_zero₃₁ T hT
    -- The unit has a left orthogonal cone, by the dual exactness argument.
    have hB : A.leftOrthogonal B := by
      intro Y f hY
      have hgf : g ≫ f = 0 := (hbij Y hY).injective (by
        rw [← Category.assoc, hcg, zero_comp, comp_zero])
      obtain ⟨b, hb⟩ : ∃ b : X⟦(1 : ℤ)⟧ ⟶ Y, f = h ≫ b :=
        Triangle.yoneda_exact₃ T hT f hgf
      let s : shiftFunctor D (1 : ℤ) ⊣ shiftFunctor D (-1 : ℤ) :=
        (shiftEquiv D (1 : ℤ)).toAdjunction
      obtain ⟨a, ha⟩ := (hbij _ (A.le_shift (-1) _ hY)).surjective
        (s.homEquiv X Y b)
      change c ≫ a = s.homEquiv X Y b at ha
      obtain ⟨a', ha'⟩ := (s.homEquiv (A.ι.obj (L.obj X)) Y).surjective a
      have hb' : b = c⟦1⟧' ≫ a' := by
        apply (s.homEquiv X Y).injective
        rw [s.homEquiv_naturality_left, ha', ha]
      rw [hb, hb', ← Category.assoc, hhc, zero_comp]
    -- Orthogonality again makes the cone vanish, so the unit is an isomorphism.
    have hh : h = 0 := (A.leftOrthogonal.rightOrthogonal.le_shift 1 _ hX) h hB
    obtain ⟨b, hb⟩ : ∃ b : B ⟶ A.ι.obj (L.obj X), 𝟙 B = b ≫ g :=
      Triangle.coyoneda_exact₃ T hT (𝟙 B) (by
        change 𝟙 B ≫ h = 0
        simpa using hh)
    have hB₀ : IsZero B := by
      apply (IsZero.iff_id_eq_zero B).2
      rw [hb, hB b (L.obj X).property, zero_comp]
    haveI : IsIso c := (Triangle.isZero₃_iff_isIso₁ T hT).1 hB₀
    exact ⟨A.ι.obj (L.obj X), (L.obj X).property, ⟨asIso c⟩⟩

/-- Stacks 0CQT: left adjointability makes the strict-full closure of `A`
stable under retracts. -/
@[stacks 0CQT]
theorem isoClosure_closedUnderRetracts (hA : A.ι.IsRightAdjoint) :
    A.isoClosure.IsStableUnderRetracts := by
  rw [isoClosure_eq A hA]
  constructor
  intro X Y r hY Z f hZ
  calc
    f = (f ≫ r.i) ≫ r.r := by simp
    _ = 0 := by rw [hY (f ≫ r.i) hZ, zero_comp]

/-- Stacks 0CQT: a strictly full left-adjointable subcategory is the right
orthogonal of its left orthogonal. -/
@[stacks 0CQT]
theorem eq_rightOrthogonal [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsRightAdjoint) :
    A = A.leftOrthogonal.rightOrthogonal := by
  simpa only [A.isoClosure_eq_self] using isoClosure_eq A hA

/-- Stacks 0CQT: a strictly full left-adjointable subcategory is stable under
retracts. -/
@[stacks 0CQT]
theorem closedUnderRetracts [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsRightAdjoint) :
    A.IsStableUnderRetracts := by
  simpa only [A.isoClosure_eq_self] using isoClosure_closedUnderRetracts A hA

end Left

namespace IsRightAdmissible

/-- A right-admissible object property is automatically stable under retracts. -/
instance stableUnderRetracts (A : ObjectProperty D) [IsRightAdmissible A] :
    A.IsStableUnderRetracts :=
  Right.closedUnderRetracts A inferInstance

end IsRightAdmissible

namespace IsLeftAdmissible

/-- A left-admissible object property is automatically stable under retracts. -/
instance stableUnderRetracts (A : ObjectProperty D) [IsLeftAdmissible A] :
    A.IsStableUnderRetracts :=
  Left.closedUnderRetracts A inferInstance

end IsLeftAdmissible

end CategoryTheory.ObjectProperty.Admissible
