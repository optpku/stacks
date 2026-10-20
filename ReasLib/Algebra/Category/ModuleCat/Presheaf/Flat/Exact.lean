module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Generators
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.CategoryTheory.Monoidal.Flat.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat objects and exact sequences of module presheaves and sheaves

This file supplies the source-facing specializations of the categorical exactness API.  The
homological content and the right-augmented exactness predicate remain owned by `CategoryTheory`;
only the module-specific flatness bridges are named here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- If the quotient in a short exact sequence of module presheaves is flat, arbitrary right
tensoring preserves the sequence. -/
@[stacks 03EX "presheaf"]
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact) [IsFlat S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := sorry

/-- In a short exact sequence of module presheaves with flat quotient, the left term is flat
exactly when the middle term is flat. -/
@[stacks 03EY "presheaf"]
theorem flat_iff_flat_of_shortExact
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact) [IsFlat S.X₃] :
    IsFlat S.X₁ ↔ IsFlat S.X₂ := sorry

/-- Tensoring a flat right-augmented resolution of module presheaves preserves its exactness. -/
@[stacks 03EZ "presheaf"]
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)} (q : ℱ 0 ⟶ 𝒬)
    (h : CategoryTheory.RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬] [∀ n, IsFlat (ℱ n)] :
    CategoryTheory.RightAugmentedExact
      (fun n ↦ (tensorRight 𝒢).obj (ℱ n))
      (fun n ↦ (tensorRight 𝒢).map (d n))
      ((tensorRight 𝒢).obj 𝒬) ((tensorRight 𝒢).map q) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- If the quotient in a short exact sequence of module sheaves is flat, arbitrary right
tensoring preserves the sequence. -/
@[stacks 03EX "sheaf", stacks 05NJ]
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : ringedSiteModuleCategory J 𝒪)
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪))
    (hS : S.ShortExact) [IsFlat 𝒪 S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := sorry

/-- In a short exact sequence of module sheaves with flat quotient, the left term is flat exactly
when the middle term is flat. -/
@[stacks 03EY "sheaf", stacks 05NK]
theorem flat_iff_flat_of_shortExact
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)}
    (hS : S.ShortExact) [IsFlat 𝒪 S.X₃] :
    IsFlat 𝒪 S.X₁ ↔ IsFlat 𝒪 S.X₂ := sorry

/-- Tensoring a flat right-augmented resolution of module sheaves preserves its exactness. -/
@[stacks 03EZ "sheaf", stacks 05NL]
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → ringedSiteModuleCategory J 𝒪)
    (d : ∀ n, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : ringedSiteModuleCategory J 𝒪} (q : ℱ 0 ⟶ 𝒬)
    (h : CategoryTheory.RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒪 𝒬] [∀ n, IsFlat 𝒪 (ℱ n)] :
    CategoryTheory.RightAugmentedExact
      (fun n ↦ (tensorRight 𝒢).obj (ℱ n))
      (fun n ↦ (tensorRight 𝒢).map (d n))
      ((tensorRight 𝒢).obj 𝒬) ((tensorRight 𝒢).map q) := sorry

end SheafOfModules.RingedSite
