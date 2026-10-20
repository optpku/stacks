/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Limits
import StacksCheckRecall

/-!
# Lemma 24.26.8

The DG derived category has arbitrary coproducts and products.  Coproducts descend directly from
DG modules; products are computed on K-injective representatives.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : DGA(𝒪))
variable {ι : Type w}

/- Lemma 24.26.8 (1) (0FT9): the DG derived category has arbitrary coproducts. -/
@[stacks 0FT9]
#check
  (inferInstance : HasCoproducts (DerivedCategory 𝒜))

/- The canonical DG-module localization preserves arbitrary coproducts. -/
#check
  (inferInstance : PreservesColimitsOfShape (Discrete ι) (DerivedCategory.Q 𝒜))

/- Lemma 24.26.8 (2) (0FT9): the DG derived category has arbitrary products. -/
@[stacks 0FT9]
#check
  (inferInstance : HasProducts (DerivedCategory 𝒜))

variable (I : ι → Mod(𝒜, d)) [HasProduct I]
variable [∀ i, Module.IsKInjective (I i)]

/- Products of K-injective representatives are preserved by the DG-module localization. -/
#check
  (inferInstance :
    PreservesLimit (Discrete.functor I) (DerivedCategory.Q 𝒜))

end SheafOfModules.RingedSite.DifferentialGradedModule
