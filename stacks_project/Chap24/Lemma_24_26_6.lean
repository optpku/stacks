module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Homology
import StacksCheckRecall

/-!
# Lemma 24.26.6

Cohomology descends through the DG derived localization.  ReasLib owns the descended functor,
its factorization through `Qh`, and the homological instance in every degree.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : DGA(𝒪))

/- Lemma 24.26.6 (1) (0FT7): degree-zero cohomology is defined on the DG derived category. -/
@[stacks 0FT7]
#check
  (DerivedCategory.homologyFunctor 𝒜 0 :
    DerivedCategory 𝒜 ⥤ ringedSiteModuleCategory J 𝒪)

/- Lemma 24.26.6 (2) (0FT7): derived cohomology recovers homotopy cohomology after `Qh`. -/
@[stacks 0FT7]
#check
  (DerivedCategory.Homology.factors 𝒜 0 :
    DerivedCategory.Qh 𝒜 ⋙ DerivedCategory.homologyFunctor 𝒜 0 ≅
      Homotopy.homologyFunctor 𝒜 0)

/- Lemma 24.26.6 (3) (0FT7): the descended cohomology functor is homological. -/
@[stacks 0FT7]
#check
  (inferInstance : (DerivedCategory.homologyFunctor 𝒜 0).IsHomological)

end SheafOfModules.RingedSite.DifferentialGradedModule
