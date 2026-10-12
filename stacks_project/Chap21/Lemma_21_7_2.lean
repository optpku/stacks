/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison
public import ReasLib.CategoryTheory.Sites.Cohomology.Derived
public import StacksCheckRecall

/-!
Lemma 21.7.2 (03YU) is a recall entry.  Under the hypotheses of Sites, Lemma 7.21.8, a functor
`u : C ⥤ D` is continuous and cocontinuous, preserves the relevant fibre products, and is fully
faithful with the terminal-object compatibility from that lemma.  The reusable data owners are
the underived and total-derived `NatIso`s in
`CategoryTheory.SiteAbelianSectionsDerived`. The `HPrime.functorIso` owner additionally records
the preservation of injectives used by the source proof, rather than hiding that condition in an
objectwise existence statement.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.SiteAbelianSectionsDerived

/- The source item has one theorem, so the checks deliberately keep the source label on the
   block rather than inventing clause numbers. -/
@[stacks 03YU "underived sections comparison"]
#check @sectionsIso

@[stacks 03YU "derived sections comparison"]
#check @derivedSectionsIso

@[stacks 03YU "total derived sections comparison"]
#check @derivedSectionsNatIso

@[stacks 03YU "terminal-compatible global sections comparison"]
#check @globalSectionsIso

@[stacks 03YU "derived global sections comparison"]
#check @derivedGlobalSectionsIso

@[stacks 03YU "total derived global sections comparison"]
#check @derivedGlobalSectionsNatIso

@[stacks 03YU "functorial derived inverse-image sections comparison"]
#check @inverseImageNatIsoOfPreservesInjectives

@[stacks 03YU "derived inverse-image sections comparison on an object"]
#check @inverseImageObjIsoOfPreservesInjectives

@[stacks 03YU "bounded-below derived-sections view"]
#check @boundedBelowIso

@[stacks 03YU "degreewise derived-sections view"]
#check @homologyIso

@[stacks 03YU "functorial objectwise cohomology comparison"]
#check @HPrime.functorIso

@[stacks 03YU "objectwise cohomology comparison"]
#check @HPrime.objIso

@[stacks 03YU "functorial global cohomology comparison"]
#check @HPrime.globalFunctorIso

@[stacks 03YU "global cohomology comparison"]
#check @HPrime.globalObjIso

end CategoryTheory.SiteAbelianSectionsDerived

namespace CategoryTheory.Sheaf

/- The standard global-cohomology projection remains a separate ReasLib owner. -/
@[stacks 03YU "derived global cohomology projection"]
#check @rightDerivedGlobalSections_isIsomorphic_functorH

end CategoryTheory.Sheaf
