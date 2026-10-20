module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.AtiyahExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.PrincipalParts
open scoped Simplicial

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A : Sheaf J CommRingCat.{u}} (B : Under A)
variable (F : ringedSiteModuleCategory J B.right) (n : ℕ)

/- 92.19.0.1: on a site, for a homomorphism of ring sheaves A ⟶ B, a sheaf of
B-modules F, and the standard resolution P_• → B of B over A, each n ≥ 0 has
the first principal-parts extension
0 → Ω(P_n/A) ⊗_{P_n} F → P¹_{P_n/A}(F) → F → 0
of P_n-modules, with F viewed as a P_n-module by restriction of scalars along
P_n → B. -/
@[stacks 09DG] #check
  (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.shortExact B F n :
    (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.sequence B F n).ShortExact)
#check (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.term B n :
  Sheaf J CommRingCat.{u})
#check (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.restrict B F n :
  ringedSiteModuleCategory J
    (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.term B n))
#check (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.sequence B F n :
  ShortComplex (ringedSiteModuleCategory J
    (SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension.term B n)))

end
