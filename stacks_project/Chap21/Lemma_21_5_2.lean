/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology.UnderlyingComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext
open SheafOfModules.RingedSite (ringSheaf unitModule)
open SheafOfModules.Cohomology

noncomputable section

universe u

/- Lemma 21.5.2 (03F2): forgetting module structure preserves first cohomology. -/
@[stacks 03F2 "underlying and module first cohomology"]
#check @SheafOfModules.Cohomology.underlyingCohomology_isomorphic_ext_one
#check @SheafOfModules.Cohomology.underlyingCohomologyFunctor_isomorphic_extFunctor_one

/- The canonical functorial data owner for the comparison. -/
#check @RingedSite.Hom.ModuleSections.globalIso

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {O : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasExt (SheafOfModules (ringSheaf J O))]
variable (F : SheafOfModules (ringSheaf J O))

#check (SheafOfModules.Cohomology.underlyingCohomology_isomorphic_ext_one
  (ringSheaf J O) F)

end
