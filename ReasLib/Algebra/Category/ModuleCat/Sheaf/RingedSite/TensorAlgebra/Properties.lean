module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of tensor-algebra sheaves

Quasi-coherence and local freeness are attached to the topology-independent tensor-algebra
owner.  Geometric specializations therefore obtain these facts through typeclass search, without
chapter-local wrapper theorems.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.TensorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (F : ringedSiteModuleCategory J 𝒪)

/-- Lemma 17.21.6 (1), tensor algebra: tensor algebras preserve quasi-coherence. -/
@[stacks 01CL "(1), tensor algebra"]
instance isQuasicoherent [F.IsQuasicoherent] :
    (sheaf 𝒪 F).IsQuasicoherent := sorry

/-- Lemma 17.21.6 (2), tensor algebra: tensor algebras preserve local freeness. -/
@[stacks 01CL "(2), tensor algebra"]
instance isLocallyFree [F.IsLocallyFree] :
    (sheaf 𝒪 F).IsLocallyFree := sorry

end SheafOfModules.RingedSite.TensorAlgebra
