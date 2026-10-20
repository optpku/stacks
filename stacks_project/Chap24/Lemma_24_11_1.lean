/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.11.1

The separator theorem and Grothendieck-abelian instance for graded module sheaves are owned by
`Graded.Module.Grothendieck`.
-/

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

/- Lemma 24.11.1 (0FRD): graded module sheaves form a Grothendieck abelian category. -/
@[stacks 0FRD]
#check @GradedModuleSheaf.instIsGrothendieckAbelian
#check @GradedModuleSheaf.hasSeparator
#check @GradedModuleSheaf.instAbelian

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} {ι : Type} [AddMonoid ι]
variable (𝒜 : GradedAlgebraSheaf 𝒪 ι)

#synth IsGrothendieckAbelian.{max u v} (Mod(𝒜))
#synth HasSeparator (Mod(𝒜))

end

end SheafOfModules.RingedSite
