module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of exterior algebras

Quasi-coherence and local freeness are attached directly to the topology-independent exterior
algebra owner.  Geometric specializations can therefore obtain these facts through typeclass
search without chapter-local wrapper theorems.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (F : ringedSiteModuleCategory J 𝒪)

/-- Lemma 17.21.6 (1) (01CL): exterior algebras preserve quasi-coherence. -/
@[stacks 01CL "(1), exterior algebra"]
instance isQuasicoherent [F.IsQuasicoherent] :
    (sheaf 𝒪 F).IsQuasicoherent := sorry

/-- Lemma 17.21.6 (2) (01CL): exterior algebras preserve local freeness. -/
@[stacks 01CL "(2), exterior algebra"]
instance isLocallyFree [F.IsLocallyFree] :
    (sheaf 𝒪 F).IsLocallyFree := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
