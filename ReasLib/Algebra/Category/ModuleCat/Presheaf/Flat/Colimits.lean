module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of flat module presheaves and sheaves

Filtered colimits and arbitrary coproducts preserve flatness.  The statements use the ambient
categorical colimit objects directly and do not install local colimit instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- A filtered colimit of flat module presheaves is flat. -/
@[stacks 03EU "presheaf filtered colimits"]
theorem isFlat_colimit_of_isFiltered
    {K : Type (max u v)} [Category K] [IsFiltered K]
    (F : K ⥤ PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ k, IsFlat (F.obj k)) :
    IsFlat (colimit F) := sorry

/-- An arbitrary coproduct of flat module presheaves is flat. -/
@[stacks 03EU "presheaf coproducts"]
theorem isFlat_coproduct
    {I : Type (max u v)}
    (F : I → PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ i, IsFlat (F i)) :
    IsFlat (∐ F) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A filtered colimit of flat module sheaves is flat. -/
@[stacks 03EU "sheaf filtered colimits", stacks 05NG "(1)"]
theorem isFlat_colimit_of_isFiltered
    {K : Type (max u v)} [Category K] [IsFiltered K]
    (F : K ⥤ ringedSiteModuleCategory J 𝒪)
    (hflat : ∀ k, IsFlat 𝒪 (F.obj k)) :
    IsFlat 𝒪 (colimit F) := sorry

/-- An arbitrary coproduct of flat module sheaves is flat. -/
@[stacks 03EU "sheaf coproducts", stacks 05NG "(2)"]
theorem isFlat_coproduct
    {I : Type (max u v)}
    (F : I → ringedSiteModuleCategory J 𝒪)
    [HasCoproduct F]
    (hflat : ∀ i, IsFlat 𝒪 (F i)) :
    IsFlat 𝒪 (∐ F) := sorry

end SheafOfModules.RingedSite
