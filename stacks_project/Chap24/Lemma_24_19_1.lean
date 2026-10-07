module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Localization
import StacksCheckRecall

/-!
# Lemma 24.19.1

The localized differential graded lower-shriek adjunction is owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Localization`.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{w}) (U : C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [(SheafOfModules.RingedSite.Localization.restriction O U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).LaxMonoidal]
variable [(SheafOfModules.RingedSite.Localization.restriction O U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]
variable (A : DGA(O))
variable (M : Mod((restrictedAlgebra O U A), d)) (N : Mod(A, d))

/- Lemma 24.19.1 (0FRW): morphisms from localized DG extension by zero correspond
canonically to morphisms into localized DG restriction. -/
@[stacks 0FRW]
#check
  (homEquiv O U A M N :
    ((lowerShriek O U A).obj M ⟶ N) ≃
      (M ⟶ (restriction O U A).obj N))

end SheafOfModules.RingedSite.DifferentialGradedModule.Localization

end
