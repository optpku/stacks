/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Trivialized
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O O' O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/- Remark 91.10.5 (1): after identifying underlying topoi, a first-order thickening is
trivial when its ring-sheaf projection admits a section. -/
@[stacks 08MG] #check (CategoryTheory.IsSplitEpi : (O' ⟶ O) → Prop)

/- Remark 91.10.5 (2): a chosen trivialization is a section of the projection. -/
@[stacks 08MG] #check (SheafOfModules.RingedSite.FirstOrderThickening.IsTrivialization :
  (O ⟶ O') → (O' ⟶ O) → Prop)

/- Remark 91.10.5 (3): the chosen section gives a splitting as sheaves of algebras. -/
@[stacks 08MG] #check (SheafOfModules.RingedSite.TrivSqZeroExt.splittingIso :
  ∀ (π : O' ⟶ O) (σ : O ⟶ O') (hσ : σ ≫ π = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero π),
    O' ≅ trivSqZeroExt O (KernelIdeal.restrict π σ))

/- Remark 91.10.5 (4): an algebra splitting respecting the original projection supplies
its chosen section. -/
@[stacks 08MG] #check (SheafOfModules.RingedSite.FirstOrderThickening.splitEpiOfIso :
  ∀ (π : O' ⟶ O) (I : SheafOfModules.{max u v} (ringSheaf J O))
    (e : O' ≅ trivSqZeroExt O I), e.hom ≫ fst O I = π → SplitEpi π)

/- Remark 91.10.5 (5): section-preserving algebra maps correspond to kernel-module maps.
The ring-sheaf convention is covariant; geometric morphisms reverse the ring-sheaf arrows. -/
@[stacks 08MG] #check (SheafOfModules.RingedSite.FirstOrderThickening.homEquiv :
  ∀ {π₁ : O₁ ⟶ O} {π₂ : O₂ ⟶ O} {σ₁ : O ⟶ O₁} {σ₂ : O ⟶ O₂},
    σ₁ ≫ π₁ = 𝟙 O → σ₂ ≫ π₂ = 𝟙 O →
    KernelIdeal.IsSquareZero π₁ → KernelIdeal.IsSquareZero π₂ →
    FirstOrderThickening.SplitHom π₁ π₂ σ₁ σ₂ ≃
      (KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂))

end

/- Remark 91.10.5: in the fixed-topos algebra-sheaf presentation, the category of trivialized
first-order thickenings is equivalent to the category of modules over the base ring sheaf. -/
@[stacks 08MG] #check (SheafOfModules.RingedSite.FirstOrderThickening.modulesEquiv :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (O : Sheaf J CommRingCat.{max u v}),
    FirstOrderThickening.Trivialized O ≌ SheafOfModules.{max u v} (ringSheaf J O))
