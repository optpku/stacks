/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.Limits
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.4.2

The reusable owners for degree evaluation, limits, colimits, abelianness, and AB5 of graded
module sheaves are provided by `Graded.Module` and `Graded.Module.Limits`.
-/

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

/- Lemma 24.4.2 (0FR0): degree evaluation and the category-level exactness and
(co)completeness properties of graded module sheaves. -/
@[stacks 0FR0]
#check @GradedModuleSheaf.eval
#check @GradedModuleSheaf.instAbelian
#check @GradedModuleSheaf.instHasLimits
#check @GradedModuleSheaf.instHasColimits
#check @GradedModuleSheaf.instAB5
#check @GradedModuleSheaf.forgetToGradedPreservesLimits
#check @GradedModuleSheaf.forgetToGradedPreservesColimits
#check @GradedModuleSheaf.evalPreservesLimits
#check @GradedModuleSheaf.evalPreservesColimits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} {ι : Type} [AddMonoid ι]
variable (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι)

#synth Abelian (Mod(𝒜))
#synth HasCoproducts (Mod(𝒜))
#synth HasColimits (Mod(𝒜))
#synth AB5 (Mod(𝒜))
#synth HasProducts (Mod(𝒜))
#synth HasLimits (Mod(𝒜))
#synth PreservesLimits (GradedModuleSheaf.eval 𝒜 n)
#synth PreservesColimits (GradedModuleSheaf.eval 𝒜 n)

end

end SheafOfModules.RingedSite
