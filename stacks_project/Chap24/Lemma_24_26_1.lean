module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homology
import StacksCheckRecall

/-!
# Lemma 24.26.1

Degreewise cohomology on DG modules is inherited from the underlying cochain complex.  ReasLib
owns its factorization through the intrinsic DG homotopy category and its homological structure.
-/

@[expose] public section

open CategoryTheory ComplexShape
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

/- Lemma 24.26.1 (1) (0FT2): cohomology of the underlying cochain complex factors through
the intrinsic DG homotopy category. -/
@[stacks 0FT2]
#check
  (Homotopy.Homology.factors 𝒜 0 :
    toK 𝒜 ⋙ Homotopy.homologyFunctor 𝒜 0 ≅
      forgetToComplex 𝒜 ⋙ HomologicalComplex.homologyFunctor
        (ringedSiteModuleCategory J 𝒪) (up ℤ) 0)

/- Lemma 24.26.1 (2) (0FT2): degree-zero cohomology is homological. -/
@[stacks 0FT2]
#check
  (inferInstance : (Homotopy.homologyFunctor 𝒜 0).IsHomological)

end SheafOfModules.RingedSite.DifferentialGradedModule
