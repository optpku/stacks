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
      Biprod.ofComponents e.hom.τ₁ S.f e.homotopyInvHomId.h₁ e.inv.τ₂ := sorry

/-- The canonical inverse candidate is the indicated matrix of short-complex components. -/
theorem stableBiprodInv_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodInv e =
      Biprod.ofComponents e.inv.τ₁ (-T.f) (-e.homotopyHomInvId.h₁) e.hom.τ₂ := sorry

/-- The forward-backward composite is a lower unipotent automorphism when the target's second
differential and the source-side degree-zero homotopy term vanish. -/
theorem stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hT : T.g = 0) (h0S : e.homotopyHomInvId.h₀ = 0) :
    stableBiprodHom e ≫ stableBiprodInv e =
      (Biprod.unipotentLower
        (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)).hom := sorry

/-- The backward-forward composite is a lower unipotent automorphism when the source's second
differential and the target-side degree-zero homotopy term vanish. -/
theorem stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    stableBiprodInv e ≫ stableBiprodHom e =
      (Biprod.unipotentLower
        (e.hom.τ₂ ≫ e.homotopyInvHomId.h₁ - e.homotopyHomInvId.h₁ ≫ e.hom.τ₁)).hom := sorry

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
    stableBiprodHom e ≫ stableBiprodCorrectedInv e = 𝟙 (S.X₁ ⊞ T.X₂) := sorry

/-- The corrected inverse is also a left inverse when both short complexes
have zero second differential and both degree-zero homotopy terms vanish. -/
theorem stableBiprodCorrectedInv_comp_stableBiprodHom
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (hT : T.g = 0)
    (h0S : e.homotopyHomInvId.h₀ = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    stableBiprodCorrectedInv e ≫ stableBiprodHom e = 𝟙 (T.X₁ ⊞ S.X₂) := sorry

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
    IsIso (stableBiprodHom e) := sorry

end CategoryTheory.ShortComplex.HomotopyEquiv
