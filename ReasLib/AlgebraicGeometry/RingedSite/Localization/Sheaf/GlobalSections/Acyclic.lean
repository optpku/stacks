module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf.GlobalSections
public import ReasLib.CategoryTheory.Sites.Cohomology.Acyclic

/-!
# Acyclicity for sections after localization at a sheaf

This leaf connects total acyclicity on a ringed site with the bounded-below
right-acyclicity of the sections functor obtained by localization at a sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

noncomputable section

universe uX vX

namespace RingedSite.Localization.AtSheaf.ModuleSections

variable (X : RingedSite.{uX, vX, max uX vX})
variable [HasSheafify X.siteTopology AddCommGrpCat.{max uX vX}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{max uX vX})]

/-- Stacks 0731 (2), for a sheaf of sets: a module sheaf with totally acyclic underlying abelian
sheaf is bounded-below right acyclic for sections after localization at any sheaf of sets. -/
@[stacks 0731 "(2), sheaf specialization"]
theorem rightAcyclic
    (K : Sheaf X.siteTopology (Type vX))
    [HasWeakSheafify (AtSheaf.site X.structureSheaf K).siteTopology
      AddCommGrpCat.{max uX vX}]
    [HasGlobalSectionsFunctor (AtSheaf.site X.structureSheaf K).siteTopology
      AddCommGrpCat.{max uX vX}]
    (F : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclic
      ((SheafOfModules.toSheaf X.structureSheaf).obj F)] :
    Functor.RightAcyclic.Bounded
      (RingedSite.Localization.AtSheaf.moduleSections X K) F := sorry

end RingedSite.Localization.AtSheaf.ModuleSections
