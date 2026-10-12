/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Truncation

/-!
# The order system of principal-parts sheaves

Principal-parts sheaves of all finite orders form a sequential inverse system.  Its transition
along `k ≤ l` is the canonical truncation from order `l` to order `k`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- The transition assigned to an identity in the opposite order category is the identity. -/
theorem system_map_id (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) (k : ℕᵒᵖ) :
    truncate phi F (leOfHom (𝟙 k).unop) = 𝟙 (sheaf phi F k.unop) := sorry

/-- The transitions assigned to composable arrows in the opposite order category compose. -/
theorem system_map_comp (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) {i j k : ℕᵒᵖ}
    (f : i ⟶ j) (g : j ⟶ k) :
    truncate phi F (leOfHom (f ≫ g).unop) =
      truncate phi F (leOfHom f.unop) ≫ truncate phi F (leOfHom g.unop) := sorry

/-- Tag 0G3W: the sequential inverse system of principal-parts sheaves over all finite orders. -/
@[stacks 0G3W "principal-parts order system"]
noncomputable def system (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    ℕᵒᵖ ⥤ ringedSiteModuleCategory J O₂ where
  obj k := sheaf phi F k.unop
  map f := truncate phi F (leOfHom f.unop)
  map_id := system_map_id phi F
  map_comp := system_map_comp phi F

end SheafOfModules.RingedSite.PrincipalParts
