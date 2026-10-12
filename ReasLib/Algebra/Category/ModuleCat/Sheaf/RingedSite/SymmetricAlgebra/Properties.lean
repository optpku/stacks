/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of symmetric-algebra sheaves

The standard local properties are attached to the topology-independent symmetric-algebra owner
and exposed as named theorems for explicit use in geometric specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (F : ringedSiteModuleCategory J 𝒪)

/-- The symmetric algebra of a quasi-coherent module sheaf is quasi-coherent. -/
@[stacks 01CL "(1), symmetric algebra"]
theorem isQuasicoherent [F.IsQuasicoherent] :
    (sheaf 𝒪 F).IsQuasicoherent := sorry

/-- The symmetric algebra of a locally free module sheaf is locally free. -/
@[stacks 01CL "(2), symmetric algebra"]
theorem isLocallyFree [F.IsLocallyFree] :
    (sheaf 𝒪 F).IsLocallyFree := sorry

end SheafOfModules.RingedSite.SymmetricAlgebra
