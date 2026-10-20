/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
public import ReasLib.CategoryTheory.Sites.Cohomology.Terminal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology and sections along a functor of sites

Objectwise cohomology is naturally the right derived sections functor, including when the
object universe of the site exceeds its morphism and coefficient universes.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe q u v

namespace CategoryTheory.SiteAbelianSectionsDerived

/-- Objectwise cohomology is naturally derived sections at unchanged coefficient universe,
independently of the object universe of the site. -/
noncomputable def heterogeneousRightDerivedSectionsIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{v})]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] (U : C) (degree : ℕ) :
    Sheaf.cohomologyAtObjectFunctor J U degree ≅
      (siteAbelianSectionsFunctor J U).rightDerived degree :=
  (NatIso.ofComponents
    (fun F ↦ Sheaf.CohomologyPresheaf.Heterogeneous.derivedSectionsIsoHPrime J U F degree)
    (fun morphism ↦
      Sheaf.CohomologyPresheaf.Heterogeneous.derivedSectionsIsoHPrime_naturality
        J U morphism degree)).symm

end CategoryTheory.SiteAbelianSectionsDerived

namespace CategoryTheory.SiteAbelianSectionsDerived.HPrime

variable {C D : Type q} [Category.{q} C] [Category.{q} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Objectwise sheaf cohomology is the corresponding right derived sections functor. -/
@[stacks 03AY "objectwise cohomology as derived sections"]
noncomputable def rightDerivedSectionsIso
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{q}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{q})] (U : C) (p : ℕ) :
    Sheaf.cohomologyAtObjectFunctor J U p ≅
      (siteAbelianSectionsFunctor J U).rightDerived p :=
  (Functor.isoWhiskerRight (Sheaf.cohomologyPresheafIso J p)
      ((evaluation Cᵒᵖ AddCommGrpCat.{q}).obj (op U))).symm ≪≫
    Sheaf.CohomologyPresheaf.derivedEvaluationIsoSections J U p

/-- Cohomology over a terminal site object is ordinary global sheaf cohomology. -/
@[stacks 03YU "cohomology over a terminal object"]
noncomputable def terminalIso
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{q}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{q})]
    (T : C) (hT : IsTerminal T) (p : ℕ) :
    Sheaf.cohomologyAtObjectFunctor J T p ≅ Sheaf.functorH J p :=
  (Abelian.extFunctor p).mapIso
    (Iso.op (GrothendieckTopology.FreeAbelianYoneda.terminalIsoInteger J T hT).symm)

/-- Objectwise cohomology after continuous pushforward is naturally isomorphic to cohomology over
the image object. Preservation of injectives is the essential derived hypothesis. -/
@[stacks 03YU "functorial objectwise cohomology comparison"]
noncomputable def functorIso
    (u : C ⥤ D) [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K]
    [HasSheafify J AddCommGrpCat.{q}] [HasSheafify K AddCommGrpCat.{q}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{q})]
    [HasExt.{q} (Sheaf K AddCommGrpCat.{q})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{q} J K).PreservesInjectiveObjects]
    (p : ℕ) (U : C) :
    u.sheafPushforwardContinuous AddCommGrpCat.{q} J K ⋙
        Sheaf.cohomologyAtObjectFunctor J U p ≅
      Sheaf.cohomologyAtObjectFunctor K (u.obj U) p :=
  Functor.isoWhiskerLeft
      (u.sheafPushforwardContinuous AddCommGrpCat.{q} J K)
      (rightDerivedSectionsIso J U p) ≪≫
    (Functor.RightDerived.precompIso
      (u.sheafPushforwardContinuous AddCommGrpCat.{q} J K)
      (siteAbelianSectionsFunctor J U) p).symm ≪≫
    SiteAbelianSectionsDerived.derivedSectionsIso u p U ≪≫
    (rightDerivedSectionsIso K (u.obj U) p).symm

/-- The component of `functorIso` at one coefficient sheaf gives the objectwise comparison. -/
@[stacks 03YU "objectwise cohomology comparison"]
noncomputable abbrev objIso
    (u : C ⥤ D) [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K]
    [HasSheafify J AddCommGrpCat.{q}] [HasSheafify K AddCommGrpCat.{q}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{q})]
    [HasExt.{q} (Sheaf K AddCommGrpCat.{q})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{q} J K).PreservesInjectiveObjects]
    (p : ℕ) (U : C) (F : Sheaf K AddCommGrpCat.{q}) :
    ((u.sheafPushforwardContinuous AddCommGrpCat.{q} J K).obj F).H' p U ≅
      F.H' p (u.obj U) :=
  (functorIso u p U).app F

/-- The global-cohomology comparison is natural in the coefficient sheaf. The terminal objects
and their compatibility with `u` are explicit data. -/
@[stacks 03YU "functorial global cohomology comparison"]
noncomputable def globalFunctorIso
    (u : C ⥤ D) [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K]
    [HasSheafify J AddCommGrpCat.{q}] [HasSheafify K AddCommGrpCat.{q}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{q})]
    [HasExt.{q} (Sheaf K AddCommGrpCat.{q})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{q} J K).PreservesInjectiveObjects]
    (T : C) (hT : IsTerminal T) (huT : IsTerminal (u.obj T)) (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{q} J K ⋙ Sheaf.functorH J p ≅
      Sheaf.functorH K p :=
  Functor.isoWhiskerLeft
      (u.sheafPushforwardContinuous AddCommGrpCat.{q} J K)
      (terminalIso J T hT p).symm ≪≫
    functorIso u p T ≪≫ terminalIso K (u.obj T) huT p

/-- The component of `globalFunctorIso` at one coefficient sheaf. -/
@[stacks 03YU "global cohomology comparison"]
noncomputable abbrev globalObjIso
    (u : C ⥤ D) [Functor.IsContinuous u J K] [Functor.IsCocontinuous u J K]
    [HasSheafify J AddCommGrpCat.{q}] [HasSheafify K AddCommGrpCat.{q}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{q})]
    [HasExt.{q} (Sheaf K AddCommGrpCat.{q})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{q} J K).PreservesInjectiveObjects]
    (T : C) (hT : IsTerminal T) (huT : IsTerminal (u.obj T))
    (p : ℕ) (F : Sheaf K AddCommGrpCat.{q}) :
    (Sheaf.functorH J p).obj
        ((u.sheafPushforwardContinuous AddCommGrpCat.{q} J K).obj F) ≅
      (Sheaf.functorH K p).obj F :=
  (globalFunctorIso u T hT huT p).app F

/- Any `sorryAx` below comes from deferred naturality or comparison laws in the imported
right-derived and cohomology-presheaf owners; the functors, components, and compositions above
are explicit data. -/

end CategoryTheory.SiteAbelianSectionsDerived.HPrime
