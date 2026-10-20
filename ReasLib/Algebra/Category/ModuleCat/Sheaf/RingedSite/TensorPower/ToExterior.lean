module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.LeftTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection from tensor powers to exterior powers

The canonical projection is defined degreewise by recursion: degree zero uses the exterior unit,
and the successor step sends the leading tensor factor through the exterior left-tensor map.
This is the topology-independent data owner for the exterior quotient of the graded tensor
algebra.
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

/-- Section 17.21 (01CF): the canonical degreewise projection from tensor powers to
exterior powers. -/
@[stacks 01CF "tensor powers project to exterior powers"]
noncomputable def toExterior
    (F : ringedSiteModuleCategory J O) :
    (n : ℕ) → sheaf O F n ⟶ ExteriorPower.sheaf O F n
  | 0 => ExteriorPower.one O F
  | n + 1 =>
      tensorHom (𝟙 F) (toExterior F n) ≫
        ExteriorPower.leftTensorMap O (𝟙 F) n

/-- In degree zero, the tensor-to-exterior projection is the exterior unit. -/
@[simp]
theorem toExterior_zero
    (F : ringedSiteModuleCategory J O) :
    toExterior O F 0 = ExteriorPower.one O F := sorry

/-- The successor tensor-to-exterior projection is obtained by projecting the shorter tensor
power and adjoining its leading factor. -/
theorem toExterior_succ
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    toExterior O F (n + 1) =
      tensorHom (𝟙 F) (toExterior O F n) ≫
        ExteriorPower.leftTensorMap O (𝟙 F) n := sorry

/-- The degreewise tensor-to-exterior projections are natural in the module sheaf. -/
theorem toExterior_naturality
    {F G : ringedSiteModuleCategory J O}
    (f : F ⟶ G) (n : ℕ) :
    toExterior O F n ≫ ExteriorPower.map O f n =
      map O f n ≫ toExterior O G n := sorry

/-- Every degreewise tensor-to-exterior projection is an epimorphism. -/
@[stacks 01CF "exterior powers are degreewise quotients of tensor powers"]
instance toExterior_epi
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    Epi (toExterior O F n) := sorry

end SheafOfModules.RingedSite.TensorPower
