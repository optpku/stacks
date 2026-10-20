/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective
import StacksCheckRecall

/-!
# Lemma 24.25.10

The extension statement is the general K-injective lifting API.  The source additionally assumes
graded injectivity, but that extra hypothesis is not needed for extension across a
quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

/- Lemma 24.25.10 (0FSX): morphisms into a K-injective DG module extend across every
quasi-isomorphism, with the triangle commuting in the intrinsic DG homotopy category. -/
@[stacks 0FSX] #check Module.IsKInjective.exists_lift (𝒜 := 𝒜)

end

end SheafOfModules.RingedSite.DifferentialGradedModule
