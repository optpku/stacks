/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : GradedAlgebraSheaf 𝒪) (ℳ 𝒩 : Mod(𝒜))

/- Definition 24.4.1 (1): a right graded 𝒜-module is a ℤ-indexed family of 𝒪-module sheaves
with 𝒪-bilinear multiplication maps ℳ^n × 𝒜^m → ℳ^{n+m} that are associative and unital
for the degree-zero identity of 𝒜. -/
@[stacks 0FQZ]
#check (GradedModuleSheaf 𝒜)

/- Definition 24.4.1 (2): a homomorphism of graded 𝒜-modules is a degreewise family of
𝒪-module maps compatible with those multiplications. -/
@[stacks 0FQZ]
#check (GradedModuleSheaf.Hom ℳ 𝒩)

/- Definition 24.4.1 (3): the category of right graded 𝒜-modules is denoted Mod(𝒜). -/
@[stacks 0FQZ]
#check (GradedModuleSheaf.moduleCategory 𝒜)

#check @GradedModuleSheaf.instCategory
#check (inferInstance : Category (Mod(𝒜)))

end

end SheafOfModules.RingedSite
