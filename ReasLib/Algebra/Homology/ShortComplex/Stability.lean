/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stable Biproducts of Short Complexes

This leaf packages the biproduct morphism associated to a homotopy equivalence
of short complexes. The chain-complex realization through a selected pair of
degrees belongs in a separate bridge layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.ShortComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {S T : ShortComplex C}

/-- Stacks 00S3: the stable biproduct morphism associated to a homotopy equivalence of
short complexes. -/
@[stacks 00S3 "stable biproduct morphism"]
noncomputable def stableBiprodHom (e : S.HomotopyEquiv T) :
    S.X₁ ⊞ T.X₂ ⟶ T.X₁ ⊞ S.X₂ :=
  biprod.lift
    (biprod.desc e.hom.τ₁ e.homotopyInvHomId.h₁)
    (biprod.desc S.f e.inv.τ₂)

/-- The canonical inverse candidate for `stableBiprodHom`. -/
noncomputable def stableBiprodInv (e : S.HomotopyEquiv T) :
    T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ :=
  biprod.lift
    (biprod.desc e.inv.τ₁ (-e.homotopyHomInvId.h₁))
    (biprod.desc (-T.f) e.hom.τ₂)

/-- The stable biproduct morphism is the indicated matrix of short-complex components. -/
theorem stableBiprodHom_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodHom e =
      Biprod.ofComponents e.hom.τ₁ S.f e.homotopyInvHomId.h₁ e.inv.τ₂ := by
  ext <;> simp [stableBiprodHom, Biprod.ofComponents]

/-- The canonical inverse candidate is the indicated matrix of short-complex components. -/
theorem stableBiprodInv_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodInv e =
      Biprod.ofComponents e.inv.τ₁ (-T.f) (-e.homotopyHomInvId.h₁) e.hom.τ₂ := by
  ext <;> simp [stableBiprodInv, Biprod.ofComponents]

/-- The forward-backward composite is a lower unipotent automorphism when the target's second
differential and the source-side degree-zero homotopy term vanish. -/
theorem stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hT : T.g = 0) (h0S : e.homotopyHomInvId.h₀ = 0) :
    stableBiprodHom e ≫ stableBiprodInv e =
      (Biprod.unipotentLower
        (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)).hom := by
  rw [stableBiprodHom_eq_ofComponents, stableBiprodInv_eq_ofComponents,
    Biprod.ofComponents_comp]
  change Biprod.ofComponents _ _ _ _ = Biprod.ofComponents (𝟙 _) 0 _ (𝟙 _)
  congr 1
  · have h := e.homotopyHomInvId.comm₁
    simp only [comp_τ₁, id_τ₁, h0S, add_zero] at h
    rw [Preadditive.comp_neg, h]
    abel
  · simp only [Preadditive.comp_neg, e.hom.comm₁₂, neg_add_cancel]
  · simp only [Preadditive.comp_neg, sub_eq_add_neg]
  · have h := e.homotopyInvHomId.comm₂
    simp only [comp_τ₂, id_τ₂, hT, zero_comp, zero_add] at h
    rw [Preadditive.comp_neg, h]
    abel

/-- The backward-forward composite is a lower unipotent automorphism when the source's second
differential and the target-side degree-zero homotopy term vanish. -/
theorem stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    stableBiprodInv e ≫ stableBiprodHom e =
      (Biprod.unipotentLower
        (e.hom.τ₂ ≫ e.homotopyInvHomId.h₁ - e.homotopyHomInvId.h₁ ≫ e.hom.τ₁)).hom := by
  rw [stableBiprodInv_eq_ofComponents, stableBiprodHom_eq_ofComponents,
    Biprod.ofComponents_comp]
  change Biprod.ofComponents _ _ _ _ = Biprod.ofComponents (𝟙 _) 0 _ (𝟙 _)
  congr 1
  · have h := e.homotopyInvHomId.comm₁
    simp only [comp_τ₁, id_τ₁, h0T, add_zero] at h
    rw [Preadditive.neg_comp, h]
    abel
  · simp only [Preadditive.neg_comp, e.inv.comm₁₂, add_neg_cancel]
  · simp only [Preadditive.neg_comp, sub_eq_add_neg]
    abel
  · have h := e.homotopyHomInvId.comm₂
    simp only [comp_τ₂, id_τ₂, hS, zero_comp, zero_add] at h
    rw [Preadditive.neg_comp, h]
    abel

/-- The explicitly corrected inverse candidate for `stableBiprodHom`.  The
lower-unipotent factor corrects the defect of the raw block inverse. -/
noncomputable def stableBiprodCorrectedInv (e : S.HomotopyEquiv T) :
    T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ :=
  stableBiprodInv e ≫
    (Biprod.unipotentLower
      (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)).inv

/-- The corrected inverse is a right inverse when the target's second
differential and the source-side degree-zero homotopy term vanish. -/
theorem stableBiprodHom_comp_stableBiprodCorrectedInv
    (e : S.HomotopyEquiv T) (hT : T.g = 0) (h0S : e.homotopyHomInvId.h₀ = 0) :
    stableBiprodHom e ≫ stableBiprodCorrectedInv e = 𝟙 (S.X₁ ⊞ T.X₂) := by
  rw [stableBiprodCorrectedInv, ← Category.assoc,
    stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower e hT h0S,
    Iso.hom_inv_id]

/-- The corrected inverse is also a left inverse when both short complexes
have zero second differential and both degree-zero homotopy terms vanish. -/
theorem stableBiprodCorrectedInv_comp_stableBiprodHom
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (hT : T.g = 0)
    (h0S : e.homotopyHomInvId.h₀ = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    stableBiprodCorrectedInv e ≫ stableBiprodHom e = 𝟙 (T.X₁ ⊞ S.X₂) := by
  haveI : Epi (stableBiprodHom e) := epi_of_epi_fac
    (stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower e hS h0T)
  apply (cancel_epi (stableBiprodHom e)).1
  rw [← Category.assoc, stableBiprodHom_comp_stableBiprodCorrectedInv e hT h0S]
  simp

/-- Stacks 00S3: the explicit stable biproduct isomorphism of short complexes
with vanishing second differentials and degree-zero homotopy terms. -/
@[stacks 00S3 "stable biproduct isomorphism"]
noncomputable def stableBiprodIso
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (hT : T.g = 0)
    (h0S : e.homotopyHomInvId.h₀ = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    S.X₁ ⊞ T.X₂ ≅ T.X₁ ⊞ S.X₂ where
  hom := stableBiprodHom e
  inv := stableBiprodCorrectedInv e
  hom_inv_id := stableBiprodHom_comp_stableBiprodCorrectedInv e hT h0S
  inv_hom_id := stableBiprodCorrectedInv_comp_stableBiprodHom e hS hT h0S h0T

/-- Stacks 00S3: the stable biproduct morphism of a homotopy equivalence is invertible when both
second differentials and both degree-zero homotopy terms vanish. -/
@[stacks 00S3 "stable biproduct isomorphism"]
theorem stableBiprodHom_isIso_of_h₀_eq_zero
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (hT : T.g = 0)
    (h0S : e.homotopyHomInvId.h₀ = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    IsIso (stableBiprodHom e) := by
  exact (stableBiprodIso e hS hT h0S h0T).isIso_hom

end CategoryTheory.ShortComplex.HomotopyEquiv
