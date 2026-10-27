/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sheaf-to-presheaf comparison

This leaf identifies the right derived functors of the inclusion of additive sheaves into
presheaves with the canonical cohomology-presheaf functors.  The comparison is owned as an
explicit natural isomorphism; the older `IsIsomorphic` statements are compatibility views.
-/

@[expose] public section

open CategoryTheory Limits Opposite ComplexShape Abelian

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{max u v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max u v}]

namespace CohomologyPresheaf

private theorem homSectionsEquiv_postcomp
    {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{v}]
    (U : D) {F G : Sheaf K AddCommGrpCat.{v}}
    (a : GrothendieckTopology.FreeAbelianYoneda.obj K U ⟶ F) (f : F ⟶ G) :
    GrothendieckTopology.FreeAbelianYoneda.homSectionsEquiv K U G (a ≫ f) =
      (siteAbelianSectionsFunctor K U).map f
        (GrothendieckTopology.FreeAbelianYoneda.homSectionsEquiv K U F a) := by
  let e := sheafSectionsNatIsoEvaluation
    (J := K) (A := AddCommGrpCat.{v}) (X := U)
  have h : GrothendieckTopology.FreeAbelianYoneda.homAddEquiv K U G (a ≫ f) =
      f.hom.app (op U)
        (GrothendieckTopology.FreeAbelianYoneda.homAddEquiv K U F a) := by
    change CategoryTheory.FreeAbelianYoneda.homAddEquiv U G.obj
        ((sheafificationAdjunction K AddCommGrpCat.{v}).homEquiv _ G (a ≫ f)) = _
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  change (e.app G).inv
      (GrothendieckTopology.FreeAbelianYoneda.homAddEquiv K U G (a ≫ f)) =
    (siteAbelianSectionsFunctor K U).map f ((e.app F).inv
      (GrothendieckTopology.FreeAbelianYoneda.homAddEquiv K U F a))
  rw [h]
  exact congrArg
    (fun k ↦ k (GrothendieckTopology.FreeAbelianYoneda.homAddEquiv K U F a))
    (e.inv.naturality f)

/-- The sheafified free abelian representable whose Hom functor computes sections over `U`. -/
abbrev generator (U : C) : Sheaf J AddCommGrpCat.{max u v} :=
  GrothendieckTopology.FreeAbelianYoneda.obj J U

/-- The additive Hom functor corepresented by the sheafified free abelian representable at
`U`. -/
abbrev homFunctor (U : C) :
    Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  preadditiveCoyoneda.obj (op (generator J U))

/-- The component of the canonical additive Hom/sections equivalence at `F`. -/
noncomputable def homSectionsObjIso
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (homFunctor J U).obj F ≅ (siteAbelianSectionsFunctor J U).obj F :=
  (GrothendieckTopology.FreeAbelianYoneda.homSectionsEquiv J U F).toAddCommGrpIso

/-- Morphisms from the sheafified free abelian representable form the sections functor. -/
noncomputable def homSectionsIso (U : C) :
    homFunctor J U ≅ siteAbelianSectionsFunctor J U :=
  NatIso.ofComponents (fun F ↦ homSectionsObjIso J U F) (fun f ↦ by
    ext a
    exact homSectionsEquiv_postcomp J U a f)

/-- The integer-indexed complex obtained by applying the corepresented Hom functor to an
injective resolution. -/
abbrev mappedHomComplex
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{max u v} ℤ :=
  ((homFunctor J U).mapHomologicalComplex (up ℤ)).obj I.cochainComplex

/-- The degree-`p` homology object of the corepresented Hom functor applied to an injective
resolution. -/
def mappedHomology
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}}
    (I : InjectiveResolution F) (p : ℕ) : AddCommGrpCat.{max u v} :=
  (mappedHomComplex J U I).homology (Int.ofNat p)

/-- The standard Hom complex from the single complex on the sheafified free abelian
representable to an injective resolution. -/
abbrev standardHomComplex
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{max u v} ℤ :=
  CochainComplex.HomComplex
    ((CochainComplex.singleFunctor _ 0).obj (generator J U)) I.cochainComplex

/-- The degree-`i` additive equivalence identifying the mapped Hom complex with the standard
single-source Hom complex. -/
noncomputable def homComplexObjIso
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (i : ℤ) :
    (mappedHomComplex J U I).X i ≅ (standardHomComplex J U I).X i :=
  (CochainComplex.HomComplex.Cochain.fromSingleEquiv
    (X := generator J U) (K := I.cochainComplex) (zero_add i)).symm.toAddCommGrpIso

/-- Applying the Hom functor from the sheafified free abelian representable to an injective
resolution gives the standard Hom complex from the corresponding single complex. -/
noncomputable def homComplexIso
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) :
    mappedHomComplex J U I ≅ standardHomComplex J U I :=
  HomologicalComplex.Hom.isoOfComponents
    (homComplexObjIso J U I) (fun i j _ ↦ by
      ext f
      exact CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i)
        j j (zero_add j))

/-- Standard Hom-complex homology is canonically its group of cohomology classes. -/
noncomputable def homologyClassIso
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (p : ℕ) :
    (standardHomComplex J U I).homology (Int.ofNat p) ≅
      AddCommGrpCat.of
        (CochainComplex.HomComplex.CohomologyClass
          ((CochainComplex.singleFunctor _ 0).obj (generator J U))
          I.cochainComplex (Int.ofNat p)) :=
  (CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor _ 0).obj (generator J U)) I.cochainComplex
    (Int.ofNat p)).toAddCommGrpIso

variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- The cohomology classes of a chosen injective resolution are canonically the corresponding
`Ext` group. -/
noncomputable def cohomologyClassExtIso
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (p : ℕ) :
    AddCommGrpCat.of
        (CochainComplex.HomComplex.CohomologyClass
          ((CochainComplex.singleFunctor _ 0).obj (generator J U))
          I.cochainComplex (Int.ofNat p)) ≅
      AddCommGrpCat.of (Ext (generator J U) F p) :=
  (I.extAddEquivCohomologyClass
    (X := generator J U) (n := p)).symm.toAddCommGrpIso

/-- Homology of the Hom functor applied to an injective resolution is canonically `Ext` from
the sheafified free abelian representable. -/
noncomputable def homologyExtIso
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (p : ℕ) :
    mappedHomology J U I p ≅
      AddCommGrpCat.of (Ext (generator J U) F p) :=
  HomologicalComplex.homologyMapIso (homComplexIso J U I) (Int.ofNat p) ≪≫
    homologyClassIso J U I p ≪≫ cohomologyClassExtIso J U I p

variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]

/-- The right derived Hom functor is canonically the homology of Hom applied to a chosen
injective resolution. -/
noncomputable def rightDerivedHomologyIso
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (p : ℕ) :
    ((homFunctor J U).rightDerived p).obj F ≅
      mappedHomology J U I p :=
  (InjectiveResolution.RightDerived.homologyIso I (homFunctor J U) p).symm

/-- The right derived Hom functor from the sheafified free abelian representable evaluates to
the corresponding `Ext` object. -/
noncomputable def rightDerivedHomIsoExt
    (U : C) {F : Sheaf J AddCommGrpCat.{max u v}}
    (I : InjectiveResolution F) (p : ℕ) :
    ((homFunctor J U).rightDerived p).obj F ≅
      AddCommGrpCat.of (Ext (generator J U) F p) :=
  rightDerivedHomologyIso J U I p ≪≫ homologyExtIso J U I p

/-- Evaluating the derived sheaf inclusion is canonically the derived sections functor. -/
noncomputable def derivedEvaluationIsoSections (U : C) (p : ℕ) :
    (sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U) ≅
      (siteAbelianSectionsFunctor J U).rightDerived p :=
  (Functor.RightDerived.postcompIso
      (sheafToPresheaf J AddCommGrpCat.{max u v})
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)) p).symm ≪≫
    NatIso.rightDerived
      (sheafSectionsNatIsoEvaluation
        (J := J) (A := AddCommGrpCat.{max u v}) (X := U)).symm p

/-- Derived sections are canonically derived Hom from the sheafified free abelian
representable. -/
noncomputable def derivedSectionsIsoHom
    (U : C) (p : ℕ) :
    (siteAbelianSectionsFunctor J U).rightDerived p ≅
      (homFunctor J U).rightDerived p :=
  (NatIso.rightDerived (homSectionsIso J U) p).symm

/-- Evaluation of the derived sheaf inclusion is canonically derived Hom from the sheafified free
abelian representable. -/
noncomputable def derivedValueIso
    (U : C) (p : ℕ) :
    (sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U) ≅
      (homFunctor J U).rightDerived p :=
  derivedEvaluationIsoSections J U p ≪≫ derivedSectionsIsoHom J U p

/-- The explicit comparison at one coefficient sheaf and one object of the site. -/
noncomputable def appIso
    (F : Sheaf J AddCommGrpCat.{max u v}) (U : C) (p : ℕ) :
    ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj
      (op U)) ≅
      (F.cohomologyPresheaf p).obj (op U) :=
  (derivedValueIso J U p).app F ≪≫
    rightDerivedHomIsoExt J U (injectiveResolution F) p

/-- On one coefficient sheaf, the derived inclusion is canonically its cohomology presheaf. -/
noncomputable def objIso
    (F : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) :
    ((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F ≅
      (cohomologyPresheafFunctor J p :
        Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}).obj F :=
  NatIso.ofComponents (fun U ↦ appIso J F U.unop p) sorry

/-- The component of the objectwise presheaf comparison at `U`. -/
@[simp]
theorem objIso_app
    (F : Sheaf J AddCommGrpCat.{max u v}) (U : C) (p : ℕ) :
    (objIso J F p).app (op U) = appIso J F U p := by
  rfl

end CohomologyPresheaf

variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]

/-- The degree-`p` right derived functor of additive sheaf
inclusion is canonically the cohomology-presheaf functor. -/
@[stacks 03AY "derived sheaf inclusion as a cohomology presheaf"]
noncomputable def cohomologyPresheafIso (p : ℕ) :
    (sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p ≅
      (cohomologyPresheafFunctor J p :
        Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  NatIso.ofComponents (fun F ↦ CohomologyPresheaf.objIso.{u, v} J F p) sorry

/-- Evaluating the forward comparison gives the canonical objectwise comparison. -/
theorem cohomologyPresheafIso_hom_app_app
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{max u v}) (U : C) :
    ((cohomologyPresheafIso J p).hom.app F).app (op U) =
      (CohomologyPresheaf.appIso J F U p).hom := by
  rfl

/-- Evaluating the inverse comparison gives the inverse canonical objectwise comparison. -/
theorem cohomologyPresheafIso_inv_app_app
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{max u v}) (U : C) :
    ((cohomologyPresheafIso J p).inv.app F).app (op U) =
      (CohomologyPresheaf.appIso J F U p).inv := by
  rfl

/-- Compatibility view of `cohomologyPresheafIso`. -/
theorem cohomologyPresheafComparison (p : ℕ) :
    IsIsomorphic
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p)
      (cohomologyPresheafFunctor J p :
        Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  exact ⟨cohomologyPresheafIso J p⟩

namespace CohomologyPresheaf.Heterogeneous

variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
variable [HasSheafify K AddCommGrpCat.{v}]

/-- Lifting the sections complex of an injective resolution identifies it with the Hom complex
from the single complex on the sheafified free abelian representable. -/
noncomputable def sectionsComplexIso
    (U : D) {F : Sheaf K AddCommGrpCat.{v}} (I : InjectiveResolution F) :
    ((AddCommGrpCat.uliftFunctor.{u, v}).mapHomologicalComplex (up ℤ)).obj
        (((siteAbelianSectionsFunctor K U).mapHomologicalComplex (up ℤ)).obj
          I.cochainComplex) ≅
      CochainComplex.HomComplex
        ((CochainComplex.singleFunctor _ 0).obj
          (GrothendieckTopology.FreeAbelianYoneda.obj K U)) I.cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun degree ↦
      ((AddEquiv.ulift).trans
        ((GrothendieckTopology.FreeAbelianYoneda.homSectionsEquiv K U
          (I.cochainComplex.X degree)).symm.trans
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv
            (X := GrothendieckTopology.FreeAbelianYoneda.obj K U)
            (K := I.cochainComplex) (zero_add degree)).symm)).toAddCommGrpIso)
    (by
      intro i j _
      ext s
      change ULift.{u} ((siteAbelianSectionsFunctor K U).obj
        (I.cochainComplex.X i)) at s
      change CochainComplex.HomComplex.δ i j
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (GrothendieckTopology.FreeAbelianYoneda.sectionsHomEquiv K U
              (I.cochainComplex.X i) s.down) (zero_add i)) =
        CochainComplex.HomComplex.Cochain.fromSingleMk
          (GrothendieckTopology.FreeAbelianYoneda.sectionsHomEquiv K U
            (I.cochainComplex.X j)
            ((siteAbelianSectionsFunctor K U).map (I.cochainComplex.d i j) s.down))
          (zero_add j)
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk _ (zero_add i) j j (zero_add j)]
      congr 1
      apply (GrothendieckTopology.FreeAbelianYoneda.homSectionsEquiv K U
        (I.cochainComplex.X j)).injective
      rw [homSectionsEquiv_postcomp]
      simp [GrothendieckTopology.FreeAbelianYoneda.sectionsHomEquiv])

variable [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{v})]
variable [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]

/-- Derived sections identify with objectwise sheaf cohomology without changing the
coefficient universe, via the Hom complex of an injective resolution. -/
noncomputable def derivedSectionsIsoHPrime
    (U : D) (F : Sheaf K AddCommGrpCat.{v}) (degree : ℕ) :
    ((siteAbelianSectionsFunctor K U).rightDerived degree).obj F ≅ F.H' degree U :=
  let resolution := injectiveResolution F
  let sections := ((siteAbelianSectionsFunctor K U).mapHomologicalComplex (up ℤ)).obj
    resolution.cochainComplex
  let homologyComparison :=
    (sections.mapHomologyIso AddCommGrpCat.uliftFunctor.{u, v} (Int.ofNat degree)).symm ≪≫
      HomologicalComplex.homologyMapIso (sectionsComplexIso K U resolution)
        (Int.ofNat degree)
  ((InjectiveResolution.RightDerived.homologyIso resolution
      (siteAbelianSectionsFunctor K U) degree).symm.addCommGroupIsoToAddEquiv.trans
    (AddEquiv.ulift.symm.trans
      (homologyComparison.addCommGroupIsoToAddEquiv.trans
        ((CochainComplex.HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor _ 0).obj
            (GrothendieckTopology.FreeAbelianYoneda.obj K U))
          resolution.cochainComplex (Int.ofNat degree)).trans
          (resolution.extAddEquivCohomologyClass
            (X := GrothendieckTopology.FreeAbelianYoneda.obj K U)
            (n := degree)).symm)))).toAddCommGrpIso

/-- The injective-resolution comparison between derived sections and objectwise cohomology
commutes with morphisms of coefficient sheaves. -/
theorem derivedSectionsIsoHPrime_naturality
    (U : D) {F G : Sheaf K AddCommGrpCat.{v}} (morphism : F ⟶ G) (degree : ℕ) :
    ((siteAbelianSectionsFunctor K U).rightDerived degree).map morphism ≫
        (derivedSectionsIsoHPrime K U G degree).hom =
      (derivedSectionsIsoHPrime K U F degree).hom ≫
        ((cohomologyPresheafFunctor K degree).map morphism).app (op U) := sorry

end CohomologyPresheaf.Heterogeneous

end CategoryTheory.Sheaf
