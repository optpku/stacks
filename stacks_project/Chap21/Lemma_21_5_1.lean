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

/- Lemma 21.5.1 (03F1): the canonical degree-one extension/cohomology comparison. -/
@[stacks 03F1 "first cohomology and module extensions"]
#check @SheafOfModules.Cohomology.ext_isomorphic_underlyingCohomology_one

/- The reusable data owner underlying the degree-one comparison. -/
#check @RingedSite.Hom.ModuleSections.globalIso

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {O : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasExt (SheafOfModules (ringSheaf J O))]
variable (F : SheafOfModules (ringSheaf J O))

#check (SheafOfModules.Cohomology.ext_isomorphic_underlyingCohomology_one
  (ringSheaf J O) F)

end
