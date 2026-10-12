/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Monoidal.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat module sheaves on ringed sites

This file specializes monoidal flatness to module sheaves and owns flat same-site morphisms of
commutative structure sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Flatness of a module sheaf, specialized from the monoidal-category owner. -/
@[stacks 03ER "sheaves of modules"]
abbrev IsFlat (𝒪 : Sheaf J CommRingCat.{w})
    (ℱ : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) : Prop :=
  CategoryTheory.MonoidalCategory.IsFlat ℱ

namespace IsFlat

/-- The exactness field of the canonical monoidal flatness owner. -/
theorem exact_tensor {𝒪 : Sheaf J CommRingCat.{w}}
    {ℱ : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} [IsFlat 𝒪 ℱ] :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪)
      (ringedSiteModuleCategory J 𝒪)
      (tensorRight ℱ) := sorry

/-- The tensor-right functor of a flat module sheaf is exact. -/
theorem exactTensor (𝒪 : Sheaf J CommRingCat.{w})
    (ℱ : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) [IsFlat 𝒪 ℱ] :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪)
      (ringedSiteModuleCategory J 𝒪)
      (tensorRight ℱ) := sorry

end IsFlat

/-- A same-site morphism of commutative structure sheaves is flat when the target unit module,
restricted to the source, is flat. -/
@[stacks 04JB "structure-map flatness"]
def IsFlatHom {𝒪 𝒪' : Sheaf J CommRingCat.{w}}
    (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat 𝒪 ((restrictionAlong α).obj (unitModule J 𝒪'))

/-- Same-site flatness is flatness of the target unit module after restriction of scalars. -/
theorem isFlatHom_iff {𝒪 𝒪' : Sheaf J CommRingCat.{w}}
    (α : 𝒪 ⟶ 𝒪') :
    IsFlatHom α ↔ IsFlat 𝒪 ((restrictionAlong α).obj (unitModule J 𝒪')) := sorry

/-- The structure module of a ringed site is flat. -/
@[instance]
theorem unit_isFlat (𝒪 : Sheaf J CommRingCat.{w})
    : IsFlat 𝒪 (unitModule J 𝒪) := sorry


end SheafOfModules.RingedSite
