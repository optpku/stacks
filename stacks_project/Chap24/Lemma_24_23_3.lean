/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Colimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.3

The reusable colimit API is split into graded-flatness, relative K-flatness, and their fixed-base
conjunction.  The two source-facing checks below record the fixed-base component of the lemma.
The additional assertion that these properties persist after every ringed-topos pullback belongs
to the geometric universal-goodness layer.
-/

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
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I Mod(A, d)]
variable [HasCoproductsOfShape I
  (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
variable [HasExactColimitsOfShape (Discrete I)
  (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
variable (F : I → Mod(A, d))

/- Lemma 24.23.3 (1), fixed-base component: arbitrary coproducts of good DG modules are good. -/
@[stacks 0FSD "(1), fixed-base coproducts"]
#check
  (IsGoodAtBase.coproduct F :
    (∀ i, IsGoodAtBase (F i)) → IsGoodAtBase (∐ F))

/- Fine-grained closure statements available without bundling the two flatness conditions. -/
#check
  (IsGradedFlat.coproduct F :
    (∀ i, IsGradedFlat (F i)) → IsGradedFlat (∐ F))
#check
  (IsKFlat.coproduct F :
    (∀ i, IsKFlat (F i)) → IsKFlat (∐ F))

end Coproduct

section FilteredColimit

variable {K : Type uI} [Category.{vI} K] [IsFiltered K]
variable [HasColimitsOfShape K Mod(A, d)]
variable [HasColimitsOfShape K
  (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
variable [HasExactColimitsOfShape K
  (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))]
variable (F : K ⥤ Mod(A, d))

/- Lemma 24.23.3 (2), fixed-base component: filtered colimits of good DG modules are good. -/
@[stacks 0FSD "(2), fixed-base filtered colimits"]
#check
  (IsGoodAtBase.colimit_of_isFiltered F :
    (∀ k, IsGoodAtBase (F.obj k)) → IsGoodAtBase (colimit F))

/- Fine-grained closure statements available without bundling the two flatness conditions. -/
#check
  (IsGradedFlat.colimit_of_isFiltered F :
    (∀ k, IsGradedFlat (F.obj k)) → IsGradedFlat (colimit F))
#check
  (IsKFlat.colimit_of_isFiltered F :
    (∀ k, IsKFlat (F.obj k)) → IsKFlat (colimit F))

end FilteredColimit

end SheafOfModules.RingedSite.DifferentialGradedModule

end
