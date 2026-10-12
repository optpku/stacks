/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.AtiyahExtension

/-!
# Atiyah extension of a module sheaf along a standard-resolution term

For a homomorphism of commutative ring sheaves and a module sheaf `F`, each
degree of the standard resolution supplies the first principal-parts short
complex of `P_n`-modules, with `F` restricted along the augmentation
`P_n ⟶ B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.PrincipalParts
open scoped Simplicial

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension

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

/- The source-facing compatibility checks for the promoted Atiyah-extension API. -/
#check (term B n : Sheaf J CommRingCat.{u})
#check (restrict B F n : ringedSiteModuleCategory J (term B n))
#check (sequence B F n : ShortComplex (ringedSiteModuleCategory J (term B n)))
#check (sequence_X₁ B F n :
  (sequence B F n).X₁ =
    FirstOrder.cotangentTensor (standardTerm A B (op ⦋n⦌)).hom (restrict B F n))
#check (sequence_X₂ B F n :
  (sequence B F n).X₂ =
    PrincipalParts.sheaf (standardTerm A B (op ⦋n⦌)).hom (restrict B F n) 1)
#check (sequence_X₃ B F n : (sequence B F n).X₃ = restrict B F n)
#check (shortExact B F n : (sequence B F n).ShortExact)

end SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension
