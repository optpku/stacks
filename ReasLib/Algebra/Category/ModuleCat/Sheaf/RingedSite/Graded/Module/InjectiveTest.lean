/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.Grothendieck
public import ReasLib.CategoryTheory.Preadditive.Injective.TestFamily

/-!
# Separator tests for graded module sheaves

The category-level `CategoryTheory.InjectiveTest` owner specializes directly to graded module
sheaves.  This leaf records the specialization and owns no parallel test-family vocabulary.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.IsGrothendieckAbelian
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable (𝒜 : GradedAlgebraSheaf 𝒪)

#synth HasSeparator (Mod(𝒜))

end

end SheafOfModules.RingedSite.GradedModuleSheaf
