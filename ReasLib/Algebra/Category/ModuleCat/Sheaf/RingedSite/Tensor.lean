/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of module sheaves on a ringed site

This file names the ambient monoidal operations on the category of module sheaves over a
commutative ring sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace SheafOfModules.RingedSite

/-- The tensor product of two sheaves of modules on a commutative ringed site. -/
@[stacks 03L6 "tensor product of module sheaves"]
noncomputable abbrev moduleTensor {𝒪 : Sheaf J CommRingCat.{w}}
    (ℱ 𝒢 : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  tensorObj ℱ 𝒢

/-- Notation for the tensor product of module sheaves. -/
scoped infixr:70 " ⊗ " => moduleTensor

/-- The tensor morphism induced by a morphism in each factor. -/
@[stacks 03L6 "tensor map of module sheaves"]
noncomputable abbrev moduleTensorMap {𝒪 : Sheaf J CommRingCat.{w}}
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  tensorHom α β

namespace Tensor

/-- The endofunctor given by tensoring module sheaves on the right by a fixed module. -/
@[stacks 03L6 "right tensor functor on module sheaves"]
noncomputable abbrev rightFunctor {𝒪 : Sheaf J CommRingCat.{w}}
    (𝒢 : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 ⥤
      ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  tensorRight 𝒢

/-- The endofunctor given by tensoring module sheaves on the left by a fixed module. -/
@[stacks 03L6 "left tensor functor on module sheaves"]
noncomputable abbrev leftFunctor {𝒪 : Sheaf J CommRingCat.{w}}
    (ℱ : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 ⥤
      ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  tensorLeft ℱ

end Tensor



end SheafOfModules.RingedSite
