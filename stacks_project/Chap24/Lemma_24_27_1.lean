/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.DeltaFunctor
import StacksCheckRecall

/-!
# The delta functor of DG-module localization

The localization from differential graded module sheaves to their intrinsic DG derived category
has the canonical connecting morphisms obtained from mapping cones of short exact sequences.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : DGA(𝒪))

/- Lemma 24.27.1 (0FTB): localization of DG-module sheaves is a delta functor on the
intrinsic DG derived category. -/
@[stacks 0FTB "delta functor of DG-module localization"]
#check
  (DerivedCategory.Delta.functor 𝒜 :
    CategoryTheory.DeltaFunctor Mod(𝒜, d) (DerivedCategory 𝒜))

#check @DerivedCategory.Delta.δ
#check @DerivedCategory.Delta.triangle_distinguished
#check @DerivedCategory.Delta.δ_naturality

end SheafOfModules.RingedSite.DifferentialGradedModule
