module

public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.CategoryTheory.Sites.GlobalSections.Evaluation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections and inverse image

This leaf owns the objectwise comparison used by continuous and cocontinuous site functors.  The
two derived functors are kept as the canonical site-level owners; the chapter need only recall this
comparison and does not choose a second model of either derived category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory.SiteAbelianSectionsDerived

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- The underived sections comparison attached to a continuous functor of sites. -/
@[stacks 03YU "underived sections comparison"]
noncomputable def sectionsIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    (U : C) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
        siteAbelianSectionsFunctor JC U ≅
      siteAbelianSectionsFunctor JD (u.obj U) :=
  Functor.isoWhiskerRight
    (u.sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{w} JC JD)
    ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U))

/-- The comparison `sectionsIso` after passage to cochain complexes and localization. This is the
concrete input used to derive the total sections comparison. -/
@[stacks 03YU "sections comparison after localization"]
noncomputable def sectionsToDerivedIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}] (U : C) :
    Functor.RightDerived.Cochain.toDerived
        (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
          siteAbelianSectionsFunctor JC U) ≅
      Functor.RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor JD (u.obj U)) :=
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (sectionsIso u U) (ComplexShape.up ℤ))
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{w} ℤ ⥤
      DerivedCategory AddCommGrpCat.{w})

/-- The total derived sections comparison induced by `sectionsIso`. -/
@[stacks 03YU "total derived sections comparison"]
noncomputable def derivedSectionsNatIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})] (U : C) :
    Functor.RightDerived.Cochain.functor
        (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
          siteAbelianSectionsFunctor JC U) ≅
      Functor.RightDerived.Cochain.functor
        (siteAbelianSectionsFunctor JD (u.obj U)) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q : CochainComplex (Sheaf JD AddCommGrpCat.{w}) ℤ ⥤
      DerivedCategory (Sheaf JD AddCommGrpCat.{w}))
    (HomologicalComplex.quasiIso (Sheaf JD AddCommGrpCat.{w}) (ComplexShape.up ℤ))
    (sectionsToDerivedIso u U)

/-- The degree-`p` derived sections comparison induced by `sectionsIso`. -/
@[stacks 03YU "derived sections comparison"]
noncomputable def derivedSectionsIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf JD AddCommGrpCat.{w})]
    (p : ℕ) (U : C) :
    ((u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
        siteAbelianSectionsFunctor JC U).rightDerived p) ≅
      (siteAbelianSectionsFunctor JD (u.obj U)).rightDerived p :=
  NatIso.rightDerived (sectionsIso u U) p

/-- The underived global-sections comparison, with the terminal-object compatibility from the
`Sites` 7.21.8 hypotheses made explicit. -/
@[stacks 03YU "global sections comparison"]
noncomputable def globalSectionsIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JC AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JD AddCommGrpCat.{w}]
    (eC : C) (hC : IsTerminal eC) (huC : IsTerminal (u.obj eC)) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
        Sheaf.Γ JC AddCommGrpCat.{w}) ≅
      Sheaf.Γ JD AddCommGrpCat.{w} :=
  Functor.isoWhiskerLeft
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD)
      (Sheaf.ΓNatIsoSheafSectionsOfTerminal JC AddCommGrpCat.{w} hC) ≪≫
    sectionsIso u eC ≪≫
      (Sheaf.ΓNatIsoSheafSectionsOfTerminal JD AddCommGrpCat.{w} huC).symm

/-- The comparison `globalSectionsIso` after passage to cochain complexes and localization. This
is the concrete input used to derive the total global-sections comparison. -/
@[stacks 03YU "global sections comparison after localization"]
noncomputable def globalSectionsToDerivedIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JC AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JD AddCommGrpCat.{w}]
    (eC : C) (hC : IsTerminal eC) (huC : IsTerminal (u.obj eC)) :
    Functor.RightDerived.Cochain.toDerived
        (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
          Sheaf.Γ JC AddCommGrpCat.{w}) ≅
      Functor.RightDerived.Cochain.toDerived (Sheaf.Γ JD AddCommGrpCat.{w}) :=
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (globalSectionsIso u eC hC huC) (ComplexShape.up ℤ))
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{w} ℤ ⥤
      DerivedCategory AddCommGrpCat.{w})

/-- The total derived global-sections comparison induced by `globalSectionsIso`. -/
@[stacks 03YU "total derived global sections comparison"]
noncomputable def derivedGlobalSectionsNatIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JC AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})] (eC : C)
    (hC : IsTerminal eC)
    (huC : IsTerminal (u.obj eC)) :
      Functor.RightDerived.Cochain.functor
        (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
          Sheaf.Γ JC AddCommGrpCat.{w}) ≅
      Functor.RightDerived.Cochain.functor (Sheaf.Γ JD AddCommGrpCat.{w}) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q : CochainComplex (Sheaf JD AddCommGrpCat.{w}) ℤ ⥤
      DerivedCategory (Sheaf JD AddCommGrpCat.{w}))
    (HomologicalComplex.quasiIso (Sheaf JD AddCommGrpCat.{w}) (ComplexShape.up ℤ))
    (globalSectionsToDerivedIso u eC hC huC)

/-- The degree-`p` derived global-sections comparison induced by `globalSectionsIso`. -/
@[stacks 03YU "derived global sections comparison"]
noncomputable def derivedGlobalSectionsIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JC AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf JD AddCommGrpCat.{w})]
    (p : ℕ) (eC : C) (hC : IsTerminal eC) (huC : IsTerminal (u.obj eC)) :
    ((u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD ⋙
        Sheaf.Γ JC AddCommGrpCat.{w}).rightDerived p) ≅
      (Sheaf.Γ JD AddCommGrpCat.{w}).rightDerived p :=
  NatIso.rightDerived (globalSectionsIso u eC hC huC) p

/-- If inverse image preserves injective abelian sheaves, derived sections
after derived inverse image are naturally isomorphic to derived sections over the image object. -/
@[stacks 03YU "functorial derived inverse image and sections"]
noncomputable def inverseImageNatIsoOfPreservesInjectives
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD).PreservesInjectiveObjects]
    (U : C) :
    siteAbelianInverseImageDerived JC JD u ⋙ siteAbelianSectionsDerived JC U ≅
      siteAbelianSectionsDerived JD (u.obj U) :=
  Functor.RightDerived.Cochain.ExactFirst.iso
      (A := Sheaf JD AddCommGrpCat.{w}) (B := Sheaf JC AddCommGrpCat.{w})
      (C := AddCommGrpCat.{w})
      (siteAbelianInverseImageExact JC JD u) (siteAbelianSectionsFunctor JC U) ≪≫
    derivedSectionsNatIso u U

/-- The component of `inverseImageNatIsoOfPreservesInjectives` at one derived coefficient
object. -/
@[stacks 03YU "derived inverse-image sections comparison on an object"]
noncomputable abbrev inverseImageObjIsoOfPreservesInjectives
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD).PreservesInjectiveObjects]
    (U : C) (M : DerivedCategory (Sheaf JD AddCommGrpCat.{w})) :
    (siteAbelianSectionsDerived JC U).obj
        ((siteAbelianInverseImageDerived JC JD u).obj M) ≅
      (siteAbelianSectionsDerived JD (u.obj U)).obj M :=
  (inverseImageNatIsoOfPreservesInjectives u U).app M

/-- Derived abelian sections over `U` commute with inverse image when the
continuous inverse-image presentation preserves injective objects. -/
@[stacks 0DD8 "abelian inverse image and sections"]
theorem inverseImageIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD).PreservesInjectiveObjects]
    (U : C) (M : DerivedCategory (Sheaf JD AddCommGrpCat.{w})) :
    IsIsomorphic
      ((siteAbelianSectionsDerived JC U).obj
        ((siteAbelianInverseImageDerived JC JD u).obj M))
      ((siteAbelianSectionsDerived JD (u.obj U)).obj M) := sorry

/-- Bounded-below derived sections commute with exact inverse image when its continuous
presentation preserves injective objects. -/
@[stacks 0DD8 "bounded-below inverse image and sections"]
theorem boundedBelowIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD).PreservesInjectiveObjects]
    (U : C) (L : DerivedCategory.Plus (Sheaf JD AddCommGrpCat.{w})) :
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived JC U).obj
        ((siteAbelianInverseImageBoundedBelowDerived JC JD u).obj L))
      ((siteAbelianSectionsBoundedBelowDerived JD (u.obj U)).obj L) := sorry

/- The bounded-below source view is a degreewise projection of the canonical unbounded
comparison above.  Keeping this as a separate theorem avoids making a particular
`DerivedCategory.homologyFunctor` degree part of the core sections functor. -/
/-- Derived sections after inverse image agree degreewise for a bounded-below object when the
continuous inverse-image presentation preserves injectives. The sections are evaluated at `U`
and `u.obj U`. -/
@[stacks 0DD8 "bounded-below derived sections comparison"]
theorem homologyIso
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf JC AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf JD AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD).PreservesInjectiveObjects]
    (U : C) (L : DerivedCategory.Plus (Sheaf JD AddCommGrpCat.{w})) (n : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{w} n).obj
        ((siteAbelianSectionsDerived JC U).obj
          ((siteAbelianInverseImageDerived JC JD u).obj (DerivedCategory.Plus.ι.obj L))))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{w} n).obj
        ((siteAbelianSectionsDerived JD (u.obj U)).obj (DerivedCategory.Plus.ι.obj L))) := sorry

end CategoryTheory.SiteAbelianSectionsDerived
