/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Decomposition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants as top exterior powers

For a finite locally free module sheaf of constant rank `r`, the annihilator determinant inside
the total exterior algebra is canonically its degree-`r` exterior power.  Both directions of the
comparison are explicit: one projects the determinant inclusion to degree `r`, while the other
uses the determinant kernel's universal property to lift the degree-`r` inclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Projection of the determinant inclusion onto the degree-`r` exterior-power summand. -/
@[stacks 0FJN "determinant projection to the top exterior power"]
noncomputable def topHom
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ) :
    sheaf F ⟶ ExteriorPower.sheaf 𝒪 F r :=
  ι F ≫ (ExteriorAlgebra.decompositionAppIso 𝒪 F).hom ≫
    Limits.Sigma.π (ExteriorPower.gradedObject 𝒪 F) r

/-- For a rank-`r` module sheaf, degree-`r` exterior forms are annihilated by further
degree-one multiplication. -/
@[reassoc, stacks 0FJN "top exterior power is annihilated by degree one"]
theorem powerι_comp_action
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    ExteriorAlgebra.powerι 𝒪 F r ≫ action F = 0 := sorry

/-- The degree-`r` exterior-power inclusion lifted through the determinant kernel. -/
@[stacks 0FJN "top exterior power lift to the determinant"]
noncomputable def topInv
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    ExteriorPower.sheaf 𝒪 F r ⟶ sheaf F :=
  lift F (ExteriorAlgebra.powerι 𝒪 F r) (powerι_comp_action 𝒪 F r)

/-- The top exterior-power lift recovers the homogeneous inclusion into the exterior algebra. -/
@[reassoc, stacks 0FJN "top exterior power lift equation"]
theorem topInv_ι
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    topInv 𝒪 F r ≫ ι F = ExteriorAlgebra.powerι 𝒪 F r := sorry

/-- Projection to the top exterior power followed by its determinant lift is the identity. -/
theorem topHom_topInv
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    topHom 𝒪 F r ≫ topInv 𝒪 F r = 𝟙 _ := sorry

/-- The determinant lift followed by projection to the top exterior power is the identity. -/
theorem topInv_topHom
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    topInv 𝒪 F r ≫ topHom 𝒪 F r = 𝟙 _ := sorry

/-- The annihilator determinant of a finite locally free rank-`r` module sheaf is canonically
its top exterior power. -/
@[stacks 0FJN "determinant is the top exterior power"]
noncomputable def topIso
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    sheaf F ≅ ExteriorPower.sheaf 𝒪 F r :=
  { hom := topHom 𝒪 F r
    inv := topInv 𝒪 F r
    hom_inv_id := topHom_topInv 𝒪 F r
    inv_hom_id := topInv_topHom 𝒪 F r }

/-- The forward determinant comparison is characterized by the homogeneous inclusion into the
exterior algebra. -/
@[reassoc, stacks 0FJN "determinant comparison inclusion equation"]
theorem topIso_hom_powerι
    (F : ringedSiteModuleCategory J 𝒪) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    (topIso 𝒪 F r).hom ≫ ExteriorAlgebra.powerι 𝒪 F r = ι F := sorry

/-- The determinant isomorphism agrees, under the top exterior-power comparisons, with the
isomorphism induced on degree `r`. -/
@[reassoc, stacks 0FJN "naturality of the determinant top exterior power comparison"]
theorem mapIso_hom_topIso
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] [IsFiniteLocallyFreeOfRank r G] :
    (mapIso e).hom ≫ (topIso 𝒪 G r).hom =
      (topIso 𝒪 F r).hom ≫ (ExteriorPower.mapIso 𝒪 e r).hom := sorry

-- The `sorryAx` in `topInv` is confined to the proof that the explicit homogeneous inclusion
-- factors through the determinant kernel.

-- The comparison's two morphisms are `topHom` and `topInv`; any `sorryAx` in the `Iso` value is
-- confined to its inverse-law fields.

end SheafOfModules.RingedSite.Determinant
