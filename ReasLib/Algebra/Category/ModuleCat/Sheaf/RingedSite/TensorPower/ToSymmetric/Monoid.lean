/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.ToSymmetric
import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded tensor-to-symmetric quotient morphism

The degreewise tensor-to-symmetric projections assemble into a morphism of Mathlib monoid objects
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

/-- The degreewise tensor-to-symmetric projection as a morphism of naturally graded objects. -/
noncomputable def toSymmetricHom (F : ringedSiteModuleCategory J O) :
    gradedObject O F ⟶ SymmetricPower.gradedObject O F :=
  fun n ↦ toSymmetric O F n

/-- The degree-`n` component of the graded tensor-to-symmetric projection. -/
@[simp]
theorem toSymmetricHom_apply
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    toSymmetricHom O F n = toSymmetric O F n := sorry

/-- The graded tensor-to-symmetric projection preserves the assembled unit. -/
theorem toSymmetricHom_one (F : ringedSiteModuleCategory J O) :
    oneHom O F ≫ toSymmetricHom O F = SymmetricPower.oneHom O F := sorry

/-- The graded tensor-to-symmetric projection preserves assembled multiplication. -/
theorem toSymmetricHom_mul (F : ringedSiteModuleCategory J O) :
    mulHom O F ≫ toSymmetricHom O F =
      (toSymmetricHom O F ⊗ₘ toSymmetricHom O F) ≫
        SymmetricPower.mulHom O F := sorry

/-- Section 17.21 (01CF): the canonical morphism from the graded tensor algebra to the graded
symmetric algebra. -/
@[stacks 01CF "graded tensor algebra projects to the symmetric algebra"]
noncomputable def toSymmetricMon (F : ringedSiteModuleCategory J O) :
    mon O F ⟶ SymmetricPower.mon O F :=
  Mon.Hom.mk' (toSymmetricHom O F) (toSymmetricHom_one O F)
    (toSymmetricHom_mul O F)

/-- The underlying graded morphism of the tensor-to-symmetric algebra map is the canonical
degreewise projection. -/
@[simp]
theorem toSymmetricMon_hom (F : ringedSiteModuleCategory J O) :
    (toSymmetricMon O F).hom = toSymmetricHom O F := sorry

/-- The tensor-to-symmetric graded algebra morphism is an epimorphism. -/
@[stacks 01CF "the symmetric algebra is a quotient of the tensor algebra"]
instance toSymmetricMon_epi (F : ringedSiteModuleCategory J O) :
    Epi (toSymmetricMon O F) := sorry

/-- Tensor-to-symmetric quotient morphisms are natural in the module sheaf. -/
theorem toSymmetricMon_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (monFunctor O).map f ≫ toSymmetricMon O G =
      toSymmetricMon O F ≫ (SymmetricPower.monFunctor O).map f := sorry

/-- The canonical quotient from the graded tensor-algebra functor to the graded
symmetric-algebra functor. -/
@[stacks 01CF "natural tensor-to-symmetric quotient"]
noncomputable def toSymmetricNatTrans :
    monFunctor O ⟶ SymmetricPower.monFunctor O where
  app F := toSymmetricMon O F
  naturality := fun {F G} f ↦ toSymmetricMon_naturality O (F := F) (G := G) f

end SheafOfModules.RingedSite.TensorPower
