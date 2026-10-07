module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.Limits

/-!
# Grothendieck structure on graded module sheaves

This leaf installs the category-level infrastructure used by injective and localization
constructions for graded module sheaves on a ringed site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- Lemma 24.11.1 (0FRD): a graded module sheaf category has a separator. -/
@[stacks 0FRD "separator"]
theorem hasSeparator
    [h_sheafify : HasSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) : HasSeparator (Mod(𝒜)) := sorry

/-- Lemma 24.11.1 (0FRD): graded module sheaves form a Grothendieck abelian category. -/
@[stacks 0FRD "Grothendieck abelian category"]
instance instIsGrothendieckAbelian
    [h_sheafify : HasSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    IsGrothendieckAbelian.{max u v} (Mod(𝒜)) := sorry

end

end SheafOfModules.RingedSite.GradedModuleSheaf
