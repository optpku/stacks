/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.ShortExact.Naturality
import StacksCheckRecall

universe u

open CategoryTheory
open scoped Module.Determinant TensorProduct

/- Lemma 50.18.2 -/
@[stacks 0H9F] #check
  (CategoryTheory.ShortComplex.ShortExact.ExteriorComparison.naturality :
    ∀ {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
      {S₁ : ShortComplex (ModuleCat.{u} R₁)}
      {S₂ : ShortComplex (ModuleCat.{u} R₂)}
      {N₁ : ModuleCat.{u} R₁} {N₂ : ModuleCat.{u} R₂},
      (φ : R₁ →+* R₂) →
      (hS₁ : S₁.ShortExact) → (hS₂ : S₂.ShortExact) →
      (F : S₁ ⟶ S₂.map (ModuleCat.restrictScalars φ)) →
      (fN : N₁ ⟶ (ModuleCat.restrictScalars φ).obj N₂) →
      (dL₁ : N₁ ⟶ S₁.X₂) → (dM₁ : N₁ ⟶ S₁.X₃) →
      (dL₂ : N₂ ⟶ S₂.X₂) → (dM₂ : N₂ ⟶ S₂.X₃) →
      (hcomm₁ : dL₁ ≫ S₁.g = dM₁) →
      (hcomm₂ : dL₂ ≫ S₂.g = dM₂) →
      (hL : dL₁ ≫ F.τ₂ = fN ≫ (ModuleCat.restrictScalars φ).map dL₂) →
      (hM : dM₁ ≫ F.τ₃ = fN ≫ (ModuleCat.restrictScalars φ).map dM₂) →
      [Module.Free R₁ N₁] → [Module.Finite R₁ N₁] →
      [Module.Free R₂ N₂] → [Module.Finite R₂ N₂] →
      [Module.Free R₁ S₁.X₃] → [Module.Finite R₁ S₁.X₃] →
      [Module.Free R₂ S₂.X₃] → [Module.Finite R₂ S₂.X₃] →
      [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ fN)] →
      [IsIso (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ F.τ₃)] →
      (hRank₁ : Module.finrank R₁ N₁ = Module.finrank R₁ S₁.X₃) →
      (hRank₂ : Module.finrank R₂ N₂ = Module.finrank R₂ S₂.X₃) →
      (p : ℕ) →
      ModuleCat.ofHom
          (CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS₁ dL₁ dM₁
            hcomm₁ hRank₁ p) ≫
          CategoryTheory.ShortComplex.ShortExact.ExteriorComparison.targetMap φ F fN p =
        ModuleCat.exteriorPower.mapRestrictScalars φ
            (CategoryTheory.ShortComplex.ShortExact.ExteriorComparison.cokernelMap
              φ F dL₁ dL₂ fN hL) p ≫
          (ModuleCat.restrictScalars φ).map
            (ModuleCat.ofHom
              (CategoryTheory.ShortComplex.ShortExact.exteriorComparison hS₂ dL₂ dM₂
                hcomm₂ hRank₂ p)))
