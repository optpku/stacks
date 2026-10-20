/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.DeltaFunctor
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.SequentialColimit
import StacksCheckRecall

/-!
# Sequential colimits of DG modules

For a sequential diagram of differential graded module sheaves, the ordinary termwise colimit
represents the homotopy colimit after intrinsic DG localization.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒜 : DGA(𝒪)}
variable (M : ℕ ⥤ Mod(𝒜, d))

/- Lemma 24.27.2 (0FTC): the localized ordinary colimit of a sequential DG-module diagram is
a homotopy colimit of the localized diagram. -/
@[stacks 0FTC "ordinary sequential colimit represents the DG homotopy colimit"]
#check
  (CategoryTheory.DeltaFunctor.SequentialColimit.isOf
      (DerivedCategory.Delta.functor 𝒜) M :
    CategoryTheory.HomotopyColimit.IsOf
      (M ⋙ DerivedCategory.Q 𝒜) ((DerivedCategory.Q 𝒜).obj (colimit M)))

#check
  (CategoryTheory.DeltaFunctor.SequentialColimit.presentation
      (DerivedCategory.Delta.functor 𝒜) M :
    CategoryTheory.HomotopyColimit.Presentation
      (M ⋙ DerivedCategory.Q 𝒜) ((DerivedCategory.Q 𝒜).obj (colimit M)))

end SheafOfModules.RingedSite.DifferentialGradedModule
