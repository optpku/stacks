/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Comma

variable {B : Type u₁} {C : Type u₂} [Category.{v₁} B] [Category.{v₂} C]
variable (G : B ⥤ C) (source target : Comma (𝟭 C) G)

/-- A comma morphism determines its base map and a morphism over the target base. -/
def toSigmaOverMap (φ : source ⟶ target) :
    Σ g : source.right ⟶ target.right,
      (Over.map (G.map g)).obj (Over.mk source.hom) ⟶ Over.mk target.hom :=
  ⟨φ.right, Over.homMk φ.left φ.w⟩

/-- A base map and a morphism over the target base determine a comma morphism. -/
def fromSigmaOverMap
    (σ : Σ g : source.right ⟶ target.right,
      (Over.map (G.map g)).obj (Over.mk source.hom) ⟶ Over.mk target.hom) :
    source ⟶ target where
  left := σ.2.left
  right := σ.1
  w := Over.w σ.2

/-- Reconstructing a comma morphism from its base map and slice morphism recovers it. -/
theorem fromSigmaOverMap_toSigmaOverMap (φ : source ⟶ target) :
    fromSigmaOverMap G source target (toSigmaOverMap G source target φ) = φ := sorry

/-- Decomposing a reconstructed comma morphism recovers the base map and slice morphism. -/
theorem toSigmaOverMap_fromSigmaOverMap
    (σ : Σ g : source.right ⟶ target.right,
      (Over.map (G.map g)).obj (Over.mk source.hom) ⟶ Over.mk target.hom) :
    toSigmaOverMap G source target (fromSigmaOverMap G source target σ) = σ := sorry

/-- Comma morphisms are equivalent to base maps together with morphisms over the target base. -/
def homEquivSigmaOverMap :
    (source ⟶ target) ≃ Σ g : source.right ⟶ target.right,
      (Over.map (G.map g)).obj (Over.mk source.hom) ⟶ Over.mk target.hom where
  toFun := toSigmaOverMap G source target
  invFun := fromSigmaOverMap G source target
  left_inv := fromSigmaOverMap_toSigmaOverMap G source target
  right_inv := toSigmaOverMap_fromSigmaOverMap G source target

variable [Limits.HasPullbacks C]

/-- Comma morphisms are equivalent to base maps together with slice morphisms into pullbacks. -/
def homEquivSigmaPullback :
    (source ⟶ target) ≃ Σ g : source.right ⟶ target.right,
      Over.mk source.hom ⟶ (Over.pullback (G.map g)).obj (Over.mk target.hom) :=
  (homEquivSigmaOverMap G source target).trans
    (Equiv.sigmaCongrRight fun g =>
      (Over.mapPullbackAdj (G.map g)).homEquiv (Over.mk source.hom) (Over.mk target.hom))

/-- The pullback decomposition of a comma morphism preserves its base map. -/
theorem homEquivSigmaPullback_fst (φ : source ⟶ target) :
    (homEquivSigmaPullback G source target φ).1 = φ.right := sorry

/-- The slice component of the pullback decomposition is the canonical mediating map. -/
theorem homEquivSigmaPullback_snd_left (φ : source ⟶ target) :
    (homEquivSigmaPullback G source target φ).2.left =
      Limits.pullback.lift φ.left source.hom φ.w := sorry

end CategoryTheory.Comma
