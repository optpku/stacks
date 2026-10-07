module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.LeftTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection from tensor powers to symmetric powers

The canonical projection is defined degreewise by recursion: degree zero uses the symmetric unit,
and the successor step sends the leading tensor factor through the symmetric left-tensor map.
This is the topology-independent data owner for the symmetric quotient of the graded tensor
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
symmetric powers. -/
@[stacks 01CF "tensor powers project to symmetric powers"]
noncomputable def toSymmetric
    (F : ringedSiteModuleCategory J O) :
    (n : ℕ) → sheaf O F n ⟶ SymmetricPower.sheaf O F n
  | 0 => SymmetricPower.one O F
  | n + 1 =>
      tensorHom (𝟙 F) (toSymmetric F n) ≫
        SymmetricPower.leftTensorMap O (𝟙 F) n

/-- In degree zero, the tensor-to-symmetric projection is the symmetric unit. -/
@[simp]
theorem toSymmetric_zero
    (F : ringedSiteModuleCategory J O) :
    toSymmetric O F 0 = SymmetricPower.one O F := sorry

/-- The successor tensor-to-symmetric projection is obtained by projecting the shorter tensor
power and adjoining its leading factor. -/
theorem toSymmetric_succ
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    toSymmetric O F (n + 1) =
      tensorHom (𝟙 F) (toSymmetric O F n) ≫
        SymmetricPower.leftTensorMap O (𝟙 F) n := sorry

/-- The degreewise tensor-to-symmetric projections are natural in the module sheaf. -/
theorem toSymmetric_naturality
    {F G : ringedSiteModuleCategory J O}
    (f : F ⟶ G) (n : ℕ) :
    toSymmetric O F n ≫ SymmetricPower.map O f n =
      map O f n ≫ toSymmetric O G n := sorry

/-- Every degreewise tensor-to-symmetric projection is an epimorphism. -/
@[stacks 01CF "symmetric powers are degreewise quotients of tensor powers"]
instance toSymmetric_epi
    (F : ringedSiteModuleCategory J O) (n : ℕ) :
    Epi (toSymmetric O F n) := sorry

end SheafOfModules.RingedSite.TensorPower
