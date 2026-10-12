/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants and localization of a ringed site

For a finite locally free module sheaf of fixed rank, restriction to a slice commutes with its
determinant.  The comparison is assembled through the top exterior power; no rank-free claim
about restriction preserving the kernel presentation of the determinant is made here.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The top exterior-power comparison for the restriction of a fixed-rank module sheaf.  This
bridge fixes the canonical slice-site infrastructure once, avoiding instance diamonds at use
sites. -/
@[stacks 0FJN "top exterior power after localized restriction"]
noncomputable def topIsoOver
    (F : ringedSiteModuleCategory J O) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    sheaf (J := J.over U) (𝒪 := O.over U) (F.over U) ≅
      ExteriorPower.sheaf (O.over U) (F.over U) r :=
  @topIso (Over U) _ (J.over U) _ _ _ _ _ _
    (O.over U) (F.over U) r
      (IsFiniteLocallyFreeOfRank.overRingedSite r F U)

/-- For a finite locally free rank-`r` module sheaf, restriction to a slice commutes with its
determinant.  The comparison is the restricted top-power isomorphism, followed by exterior-power
localization and the inverse top-power isomorphism on the slice. -/
@[stacks 0FJN "fixed-rank determinant localization"]
noncomputable def overIsoOfRank
    (F : ringedSiteModuleCategory J O) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    (sheaf F).over U ≅ sheaf (J := J.over U) (𝒪 := O.over U) (F.over U) :=
  (Localization.restriction O U).mapIso (topIso O F r) ≪≫
    ExteriorPower.overIso O U F r ≪≫
      (topIsoOver O U F r).symm

/-- The determinant localization comparison is the exterior-power localization comparison after
identifying both determinants with their rank-`r` top exterior powers. -/
@[reassoc, stacks 0FJN "fixed-rank determinant localization and top exterior powers"]
theorem overIsoOfRank_hom_topIso
    (F : ringedSiteModuleCategory J O) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    (overIsoOfRank O U F r).hom ≫
        (topIsoOver O U F r).hom =
      SheafOfModules.Hom.over (topIso O F r).hom U ≫
        (ExteriorPower.overIso O U F r).hom := sorry

/-- The forward determinant localization map carries the restricted determinant inclusion to the
determinant inclusion on the slice under exterior-algebra localization. -/
@[reassoc, stacks 0FJN "fixed-rank determinant localization inclusion"]
theorem overIsoOfRank_hom_ι
    (F : ringedSiteModuleCategory J O) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] :
    (overIsoOfRank O U F r).hom ≫
        ι (J := J.over U) (𝒪 := O.over U) (F.over U) =
      SheafOfModules.Hom.over (ι F) U ≫
        (ExteriorAlgebra.overIso O U F).hom := sorry

/-- The fixed-rank determinant localization comparison is natural with respect to module-sheaf
isomorphisms. -/
@[reassoc, stacks 0FJN "naturality of fixed-rank determinant localization"]
theorem overIsoOfRank_naturality
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r F] [IsFiniteLocallyFreeOfRank r G] :
    SheafOfModules.Hom.over (mapIso e).hom U ≫
        (overIsoOfRank O U G r).hom =
      (overIsoOfRank O U F r).hom ≫
        (mapIso (J := J.over U) (𝒪 := O.over U)
          ((Localization.restriction O U).mapIso e)).hom := sorry

-- The comparison is an explicit composite of three canonical isomorphisms; any `sorryAx` in
-- its value comes only from proof-law fields of those existing isomorphisms.

end SheafOfModules.RingedSite.Determinant
