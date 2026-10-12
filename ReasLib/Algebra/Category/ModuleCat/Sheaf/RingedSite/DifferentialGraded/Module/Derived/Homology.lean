/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology on the DG derived category

Cohomology descends from the intrinsic DG homotopy category along the quasi-isomorphism
localization. Both the homotopy-level and module-level factorization isomorphisms are exposed.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib keeps this canonical finite-biproduct construction non-global.  Derived cohomology
-- must elaborate against the same pinned triangulated and localization structures.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Every DG homotopy quasi-isomorphism is inverted by cohomology in degree `n`. -/
theorem homotopyHomology_inverts (𝒜 : DGA(𝒪)) (n : ℤ) :
    (Homotopy.quasiIso 𝒜).IsInvertedBy
      (Homotopy.homologyFunctor 𝒜 n) := sorry

/-- The degree-`n` cohomology functor on the DG derived category. -/
@[stacks 0FT7]
noncomputable def homologyFunctor (𝒜 : DGA(𝒪)) (n : ℤ) :
    DerivedCategory 𝒜 ⥤ ringedSiteModuleCategory J 𝒪 :=
  Localization.lift 𝒜 (Homotopy.homologyFunctor 𝒜 n)
    (homotopyHomology_inverts 𝒜 n)

namespace Homology

/-- Derived cohomology factors cohomology on the DG homotopy category through `Qh`. -/
@[stacks 0FT7]
noncomputable def factors (𝒜 : DGA(𝒪)) (n : ℤ) :
    Qh 𝒜 ⋙ homologyFunctor 𝒜 n ≅
      Homotopy.homologyFunctor 𝒜 n :=
  Localization.facIso 𝒜 (Homotopy.homologyFunctor 𝒜 n)
    (homotopyHomology_inverts 𝒜 n)

/-- Derived cohomology also factors the cohomology of the underlying cochain complex directly
from the category of DG modules. -/
noncomputable def moduleFactors (𝒜 : DGA(𝒪)) (n : ℤ) :
    Q 𝒜 ⋙ homologyFunctor 𝒜 n ≅
      forgetToComplex 𝒜 ⋙
        HomologicalComplex.homologyFunctor
          (ringedSiteModuleCategory J 𝒪) (up ℤ) n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toK 𝒜) (factors 𝒜 n) ≪≫
    Homotopy.Homology.factors 𝒜 n

/-- Every degreewise cohomology functor on the DG derived category is homological. -/
@[stacks 0FT7]
instance isHomological (𝒜 : DGA(𝒪)) (n : ℤ) :
    (homologyFunctor 𝒜 n).IsHomological := sorry

end Homology

end


end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory
