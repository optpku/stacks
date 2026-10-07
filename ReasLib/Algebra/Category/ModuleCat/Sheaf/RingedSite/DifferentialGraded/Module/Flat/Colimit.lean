module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Flat.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of flat differential graded modules

This file specializes the generic cochain-monoid bimodule API to right DG modules on a ringed
site.  The coefficient, indexing-object, and indexing-morphism universes are independent.  The
extra shaped-colimit hypotheses are therefore explicit instead of silently restricting diagrams
to the default universe of the DG-module category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w uI vI

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}

namespace IsGradedFlat

/-- Exact colimits of graded-flat right DG modules are graded-flat.  This is the ringed-site
specialization of `CategoryTheory.Bimod.IsGradedFlat.colimit_of_exact`. -/
@[stacks 0FSD "ringed-site graded-flat exact colimits"]
theorem colimit_of_exact {K : Type uI} [Category.{vI} K]
    [HasColimitsOfShape K Mod(A, d)]
    [HasColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : K ⥤ Mod(A, d)) (hF : ∀ k, IsGradedFlat (F.obj k)) :
    IsGradedFlat (colimit F) := sorry

/-- Filtered colimits of graded-flat right DG modules are graded-flat whenever colimits of the
specified universe size exist and are exact in the coefficient module category. -/
@[stacks 0FSD "ringed-site graded-flat filtered colimits"]
theorem colimit_of_isFiltered {K : Type uI} [Category.{vI} K] [IsFiltered K]
    [HasColimitsOfShape K Mod(A, d)]
    [HasColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : K ⥤ Mod(A, d)) (hF : ∀ k, IsGradedFlat (F.obj k)) :
    IsGradedFlat (colimit F) := sorry

/-- Coproducts of graded-flat right DG modules are graded-flat whenever coproducts of the specified
universe size exist and are exact in the coefficient module category. -/
@[stacks 0FSD "ringed-site graded-flat coproducts"]
theorem coproduct {I : Type uI}
    [HasCoproductsOfShape I Mod(A, d)]
    [HasCoproductsOfShape I
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape (Discrete I)
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : I → Mod(A, d)) (hF : ∀ i, IsGradedFlat (F i)) :
    IsGradedFlat (∐ F) := sorry

end IsGradedFlat

namespace IsKFlat

/-- Exact colimits of relatively K-flat right DG modules are relatively K-flat.  This is the
ringed-site specialization of `CategoryTheory.Bimod.IsKFlat.colimit_of_exact`. -/
@[stacks 0FSD "ringed-site K-flat exact colimits"]
theorem colimit_of_exact {K : Type uI} [Category.{vI} K]
    [HasColimitsOfShape K Mod(A, d)]
    [HasColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : K ⥤ Mod(A, d)) (hF : ∀ k, IsKFlat (F.obj k)) :
    IsKFlat (colimit F) := sorry

/-- Filtered colimits of relatively K-flat right DG modules are relatively K-flat whenever
colimits of the specified universe size exist and are exact in the coefficient module category. -/
@[stacks 0FSD "ringed-site K-flat filtered colimits"]
theorem colimit_of_isFiltered {K : Type uI} [Category.{vI} K] [IsFiltered K]
    [HasColimitsOfShape K Mod(A, d)]
    [HasColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : K ⥤ Mod(A, d)) (hF : ∀ k, IsKFlat (F.obj k)) :
    IsKFlat (colimit F) := sorry

/-- Coproducts of relatively K-flat right DG modules are relatively K-flat whenever coproducts of
the specified universe size exist and are exact in the coefficient module category. -/
@[stacks 0FSD "ringed-site K-flat coproducts"]
theorem coproduct {I : Type uI}
    [HasCoproductsOfShape I Mod(A, d)]
    [HasCoproductsOfShape I
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape (Discrete I)
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : I → Mod(A, d)) (hF : ∀ i, IsKFlat (F i)) :
    IsKFlat (∐ F) := sorry

end IsKFlat

namespace IsGoodAtBase

/-- Exact colimits of fixed-base-good right DG modules remain fixed-base-good.  This is the
ringed-site specialization of `CategoryTheory.Bimod.IsGoodAtBase.colimit_of_exact`. -/
@[stacks 0FSD "ringed-site fixed-base-good exact colimits"]
theorem colimit_of_exact {K : Type uI} [Category.{vI} K]
    [HasColimitsOfShape K Mod(A, d)]
    [HasColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : K ⥤ Mod(A, d)) (hF : ∀ k, IsGoodAtBase (F.obj k)) :
    IsGoodAtBase (colimit F) := sorry

/-- Filtered colimits of fixed-base-good right DG modules remain fixed-base-good whenever
colimits of the specified universe size exist and are exact in the coefficient module category. -/
@[stacks 0FSD "ringed-site fixed-base-good filtered colimits"]
theorem colimit_of_isFiltered {K : Type uI} [Category.{vI} K] [IsFiltered K]
    [HasColimitsOfShape K Mod(A, d)]
    [HasColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape K
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : K ⥤ Mod(A, d)) (hF : ∀ k, IsGoodAtBase (F.obj k)) :
    IsGoodAtBase (colimit F) := sorry

/-- Coproducts of fixed-base-good right DG modules remain fixed-base-good whenever coproducts of
the specified universe size exist and are exact in the coefficient module category. -/
@[stacks 0FSD "ringed-site fixed-base-good coproducts"]
theorem coproduct {I : Type uI}
    [HasCoproductsOfShape I Mod(A, d)]
    [HasCoproductsOfShape I
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    [HasExactColimitsOfShape (Discrete I)
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
    (F : I → Mod(A, d)) (hF : ∀ i, IsGoodAtBase (F i)) :
    IsGoodAtBase (∐ F) := sorry

end IsGoodAtBase

end SheafOfModules.RingedSite.DifferentialGradedModule

end
