/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of almost cocontinuous pushforward

Almost cocontinuity promotes the continuous pushforward of additive and module
sheaves to an exact functor.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂ w z

namespace CategoryTheory.Functor.IsAlmostCocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [HasSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JD AddCommGrpCat.{w}]
variable [HasSheafify JD AddCommGrpCat.{w}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]

/-- Continuous pushforward along an almost cocontinuous functor is exact on sheaves of abelian
groups. -/
@[stacks 04BD "abelian sheaves"]
theorem pushforwardContinuous_exact
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    exactFunctor (Sheaf JD AddCommGrpCat.{w}) (Sheaf JC AddCommGrpCat.{w})
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD) := sorry

/-- Continuous pushforward along an almost cocontinuous functor preserves
finite limits of sheaves of abelian groups. -/
instance pushforwardContinuous_preservesFiniteLimits
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    PreservesFiniteLimits
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD) := sorry

/-- Continuous pushforward along an almost cocontinuous functor preserves
finite colimits of sheaves of abelian groups. -/
instance pushforwardContinuous_preservesFiniteColimits
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    PreservesFiniteColimits
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD) := sorry

/-- The exact continuous pushforward on sheaves of abelian groups, bundled
for downstream exact-functor constructions. -/
def pushforwardContinuousExactFunctor
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    Sheaf JD AddCommGrpCat.{w} ⥤ₑ Sheaf JC AddCommGrpCat.{w} :=
  ⟨u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD,
    pushforwardContinuous_exact u⟩

/-- Pushforward of module sheaves is exact when its underlying functor of sites is continuous and
almost cocontinuous. -/
@[stacks 04BD "module sheaves"]
theorem sheafOfModules_pushforward_exact
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    exactFunctor (SheafOfModules.{z} 𝒪D) (SheafOfModules.{z} 𝒪C)
      (SheafOfModules.pushforward.{z} φ) := sorry

/-- Pushforward of module sheaves along an almost cocontinuous site functor
preserves finite limits. -/
instance sheafOfModules_pushforward_preservesFiniteLimits
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} φ) := sorry

/-- Pushforward of module sheaves along an almost cocontinuous site functor
preserves finite colimits. -/
instance sheafOfModules_pushforward_preservesFiniteColimits
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} φ) := sorry

/-- The exact module-sheaf pushforward, bundled for downstream exact-functor
constructions. -/
noncomputable def sheafOfModulesPushforwardExactFunctor
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    SheafOfModules.{z} 𝒪D ⥤ₑ SheafOfModules.{z} 𝒪C :=
  ⟨SheafOfModules.pushforward.{z} φ,
    sheafOfModules_pushforward_exact u 𝒪C 𝒪D φ⟩

end CategoryTheory.Functor.IsAlmostCocontinuous
