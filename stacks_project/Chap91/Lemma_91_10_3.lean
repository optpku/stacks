/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_10_3_IsoClass
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism classes of mixed-scalar extensions with prescribed infinitesimal map

On a first-order thickening of ringed topoi, after identifying underlying topoi, the
isomorphism classes of mixed-scalar extensions with a prescribed infinitesimal map form a
principal homogeneous space under Ext¹ of 𝒪-modules, whenever at least one such extension
exists.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open CategoryTheory.Abelian (Ext)

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [hπ : IsFirstOrderThickening π]
variable {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c : moduleTensor (ideal π) F ⟶ K}
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- Lemma 91.10.3: Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a first-order thickening of ringed
topoi. After identifying underlying topoi as a same-site map π : 𝒪' ⟶ 𝒪, assume given
𝒪-modules ℱ, 𝒦 and an 𝒪-linear map c : ℐ ⊗ ℱ ⟶ 𝒦. If there exists a sequence
0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0 as in 91.10.0.1 with c_ℱ' = c, then the set of isomorphism classes
of these extensions is principal homogeneous under Ext ℱ 𝒦 1. -/
@[stacks 08ME]
theorem isoClass_principalHomogeneous
    (h_exists : Nonempty (ModuleExtension hπ.isSquareZero F K c))
    (E E' : IsoClass c) :
    ∃! x : Ext F K 1,
      ∀ ξ : ExtensionClass K F, ExtensionClass.toExt ξ = x ↔ vadd ξ E = E' := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
