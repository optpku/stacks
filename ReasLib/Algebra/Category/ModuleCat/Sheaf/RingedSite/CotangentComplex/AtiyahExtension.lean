/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder

/-!
# Atiyah extensions along standard-resolution terms

For a homomorphism of commutative ring sheaves and a module sheaf `F`, each degree of the
standard resolution supplies the first principal-parts short complex of `P_n`-modules, with
`F` restricted along the augmentation `P_n ⟶ B`.
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
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A : Sheaf J CommRingCat.{u}} (B : Under A)
variable (F : ringedSiteModuleCategory J B.right) (n : ℕ)

/-- The degree-`n` ring sheaf `P_n` of the standard resolution of `B` over `A`. -/
abbrev term : Sheaf J CommRingCat.{u} :=
  (standardTerm A B (op ⦋n⦌)).right

/-- The `P_n`-module obtained by restricting scalars of `F` along the standard-resolution
augmentation `P_n ⟶ B`. -/
abbrev restrict : ringedSiteModuleCategory J (term B n) :=
  (restrictionAlong (standardAugmentation A B (op ⦋n⦌))).obj F

/-- The first principal-parts short complex of `P_n`-modules
`Ω(P_n/A) ⊗_{P_n} F ⟶ P¹_{P_n/A}(F) ⟶ F` associated to the degree-`n` term of the
standard resolution of `B` over `A`. -/
def sequence : ShortComplex (ringedSiteModuleCategory J (term B n)) :=
  FirstOrder.sequence (standardTerm A B (op ⦋n⦌)).hom (restrict B F n)

/-- The left term of the degree-`n` Atiyah extension is `Ω(P_n/A) ⊗_{P_n} F`. -/
theorem sequence_X₁ :
    (sequence B F n).X₁ =
      FirstOrder.cotangentTensor (standardTerm A B (op ⦋n⦌)).hom (restrict B F n) := sorry

/-- The middle term of the degree-`n` Atiyah extension is `P¹_{P_n/A}(F)`. -/
theorem sequence_X₂ :
    (sequence B F n).X₂ =
      PrincipalParts.sheaf (standardTerm A B (op ⦋n⦌)).hom (restrict B F n) 1 := sorry

/-- The right term of the degree-`n` Atiyah extension is `F`, as a `P_n`-module. -/
theorem sequence_X₃ : (sequence B F n).X₃ = restrict B F n := sorry

/-- The degree-`n` Atiyah extension is a short exact sequence of `P_n`-modules. -/
theorem shortExact [HasSheafify J AddCommGrpCat.{u}] :
    (sequence B F n).ShortExact := sorry

end SheafOfModules.RingedSite.CotangentComplex.AtiyahExtension
