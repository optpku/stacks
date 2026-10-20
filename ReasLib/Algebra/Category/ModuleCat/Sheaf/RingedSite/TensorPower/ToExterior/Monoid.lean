/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.ToExterior
import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded tensor-to-exterior quotient morphism

The degreewise tensor-to-exterior projections assemble into a morphism of Mathlib monoid objects
in naturally graded module sheaves. Naturality packages these quotient morphisms as a natural
transformation of graded algebra functors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The degreewise tensor-to-exterior projection as a morphism of naturally graded objects. -/
noncomputable def toExteriorHom (F : ringedSiteModuleCategory J O) :
    gradedObject O F ⟶ ExteriorPower.gradedObject O F :=
  fun n ↦ toExterior O F n

/-- The degree-`n` component of the graded tensor-to-exterior projection. -/
@[simp]
theorem toExteriorHom_apply
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    toExteriorHom O F n = toExterior O F n := sorry

/-- The graded tensor-to-exterior projection preserves the assembled unit. -/
theorem toExteriorHom_one (F : ringedSiteModuleCategory J O) :
    oneHom O F ≫ toExteriorHom O F = ExteriorPower.oneHom O F := sorry

/-- The graded tensor-to-exterior projection preserves assembled multiplication. -/
theorem toExteriorHom_mul (F : ringedSiteModuleCategory J O) :
    mulHom O F ≫ toExteriorHom O F =
      (toExteriorHom O F ⊗ₘ toExteriorHom O F) ≫
        ExteriorPower.mulHom O F := sorry

/-- Section 17.21 (01CF): the canonical morphism from the graded tensor algebra to the graded
exterior algebra. -/
@[stacks 01CF "graded tensor algebra projects to the exterior algebra"]
noncomputable def toExteriorMon (F : ringedSiteModuleCategory J O) :
    mon O F ⟶ ExteriorPower.mon O F :=
  Mon.Hom.mk' (toExteriorHom O F) (toExteriorHom_one O F)
    (toExteriorHom_mul O F)

/-- The underlying graded morphism of the tensor-to-exterior algebra map is the canonical
degreewise projection. -/
@[simp]
theorem toExteriorMon_hom (F : ringedSiteModuleCategory J O) :
    (toExteriorMon O F).hom = toExteriorHom O F := sorry

/-- The tensor-to-exterior graded algebra morphism is an epimorphism. -/
@[stacks 01CF "the exterior algebra is a quotient of the tensor algebra"]
instance toExteriorMon_epi (F : ringedSiteModuleCategory J O) :
    Epi (toExteriorMon O F) := sorry

/-- Tensor-to-exterior quotient morphisms are natural in the module sheaf. -/
theorem toExteriorMon_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (monFunctor O).map f ≫ toExteriorMon O G =
      toExteriorMon O F ≫ (ExteriorPower.monFunctor O).map f := sorry

/-- The canonical quotient from the graded tensor-algebra functor to the graded
exterior-algebra functor. -/
@[stacks 01CF "natural tensor-to-exterior quotient"]
noncomputable def toExteriorNatTrans :
    monFunctor O ⟶ ExteriorPower.monFunctor O where
  app F := toExteriorMon O F
  naturality := fun {F G} f ↦ toExteriorMon_naturality O (F := F) (G := G) f

end SheafOfModules.RingedSite.TensorPower
