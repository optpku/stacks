/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derivation.Representability
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative derivations on a ringed site

The public type is a thin sheaf-level view of mathlib's presheaf derivation owner.  It is generic
in the site; geometric namespaces only need bridge notation and specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- The type of `φ`-derivations from `O₂` to an `O₂`-module sheaf `F`. -/
@[stacks 04BK, stacks 01UN "topological-space specialization"]
abbrev RelativeDerivation (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (RingedSite.ringSheaf J O₂)) : Type _ :=
  PresheafOfModules.Derivation' F.val φ.hom

end SheafOfModules

namespace RelativeDerivation

scoped notation "Der[" φ " ; " F "]" => SheafOfModules.RelativeDerivation φ F

end RelativeDerivation

open scoped RelativeDerivation

namespace SheafOfModules.RelativeDerivation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- Postcomposition sends a relative derivation to a derivation with a new target module sheaf. -/
def map (φ : O₁ ⟶ O₂)
    {F G : SheafOfModules (RingedSite.ringSheaf J O₂)}
    (f : F ⟶ G) : Der[φ ; F] ⟶ Der[φ ; G] :=
  PresheafOfModules.Derivation'.map φ.hom f.val

/-- Postcomposition by an identity is the identity on relative derivations. -/
@[simp]
theorem map_id (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (RingedSite.ringSheaf J O₂)) :
    map φ (𝟙 F) = 𝟙 (Der[φ ; F]) := sorry

/-- Successive postcomposition of relative derivations agrees with composition of module-sheaf
morphisms. -/
@[simp]
theorem map_comp (φ : O₁ ⟶ O₂)
    {F G H : SheafOfModules (RingedSite.ringSheaf J O₂)}
    (f : F ⟶ G) (g : G ⟶ H) :
    map φ (f ≫ g) = map φ f ≫ map φ g := sorry

/-- Relative derivations as a Type-valued functor of the target module sheaf. -/
@[stacks 04BK "relative derivations as a functor",
  stacks 01UN "topological-space specialization"]
noncomputable def functor (φ : O₁ ⟶ O₂) :
    SheafOfModules (RingedSite.ringSheaf J O₂) ⥤ Type _ where
  obj F := Der[φ ; F]
  map f := map φ f
  map_id F := map_id φ F
  map_comp f g := map_comp φ f g

/-- The functorial action on a relative derivation is postcomposition. -/
@[simp]
theorem functor_map_apply (φ : O₁ ⟶ O₂)
    {F G : SheafOfModules (RingedSite.ringSheaf J O₂)}
    (f : F ⟶ G) (D : Der[φ ; F]) :
    (functor φ).map f D = D.postcomp f.val := sorry

end SheafOfModules.RelativeDerivation
