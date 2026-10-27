/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Augmentation
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Refinement

/-!
# Fixed-target hypercovering Cech cohomology

The presheaf-target Cech construction is the primary owner.  This leaf specializes it along
`Hypercovering.toPresheafTargetFunctor` and retains only the fixed-target product-sections and
represented-target consequences.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering.Cech

open AlgebraicTopology Limits Opposite

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {X : C}

/-- The fixed-target Cech complex is the generic presheaf-target complex of the represented
hypercovering. -/
abbrev complexInCoefficients (K : Hypercovering.{w} J X) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  HypercoveringOf.Cech.complexInCoefficients K.toPresheafTarget

/-- Fixed-target Cech cohomology is the generic presheaf-target cohomology of the represented
hypercovering. -/
abbrev cohomologyInCoefficients (K : Hypercovering.{w} J X) (p : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w} :=
  HypercoveringOf.Cech.cohomologyInCoefficients K.toPresheafTarget p

/-- The Cech complex of a fixed-target hypercovering with fixed coefficients. -/
abbrev complex (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  HypercoveringOf.Cech.complex K.toPresheafTarget I

/-- The degree-`p` Cech cohomology object of a fixed-target hypercovering. -/
abbrev cohomology (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p : ℕ) :
    AddCommGrpCat.{max u v w} :=
  HypercoveringOf.Cech.cohomology K.toPresheafTarget I p

/-- A fixed-target hypercovering morphism induces the generic contravariant Cech complex map. -/
noncomputable def complexMap {K L : Hypercovering.{w} J X} (f : K ⟶ L)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    complex L I ⟶ complex K I :=
  HypercoveringOf.Cech.complexMap (Hypercovering.Hom.toPresheafTarget f) I

/-- A fixed-target hypercovering morphism induces the generic contravariant map on Cech
cohomology. -/
noncomputable def cohomologyMap {K L : Hypercovering.{w} J X} (f : K ⟶ L)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p : ℕ) :
    cohomology L I p ⟶ cohomology K I p :=
  HypercoveringOf.Cech.cohomologyMap (Hypercovering.Hom.toPresheafTarget f) I p

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-target Cech cohomology sends an identity hypercovering map to the identity. -/
theorem cohomologyMap_id (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p : ℕ) :
    cohomologyMap (𝟙 K) I p = 𝟙 _ := by
  have h : HypercoveringOf.Hom.toSimplicialPresheaf
      (Hypercovering.Hom.toPresheafTarget (𝟙 K)) = 𝟙 _ := by
    change Functor.whiskerRight
      (Hypercovering.Hom.toSimplicialFamily (𝟙 K)) FormalCoproduct.toPresheaf = 𝟙 _
    have h₀ : Hypercovering.Hom.toSimplicialFamily (𝟙 K) = 𝟙 K.simplicialFamily :=
      Functor.whiskerRight_id' SemiRepresentableFamily.OverFamily.forget
    exact (congrArg (fun t ↦ Functor.whiskerRight t FormalCoproduct.toPresheaf) h₀).trans
      (Functor.whiskerRight_id' FormalCoproduct.toPresheaf)
  dsimp only [cohomologyMap, HypercoveringOf.Cech.cohomologyMap,
    HypercoveringOf.Cech.complexMap]
  rw [h, NatTrans.rightOp_id, Functor.whiskerRight_id']
  exact (congrArg (fun t ↦ HomologicalComplex.homologyMap t p)
    ((alternatingCofaceMapComplex _).map_id _)).trans
      (HomologicalComplex.homologyMap_id _ p)

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-target Cech cohomology maps respect composition contravariantly. -/
theorem cohomologyMap_comp {K L M : Hypercovering.{w} J X}
    (f : K ⟶ L) (g : L ⟶ M)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p : ℕ) :
    cohomologyMap (f ≫ g) I p =
      cohomologyMap g I p ≫ cohomologyMap f I p := by
  have h : HypercoveringOf.Hom.toSimplicialPresheaf
      (Hypercovering.Hom.toPresheafTarget (f ≫ g)) =
      HypercoveringOf.Hom.toSimplicialPresheaf (Hypercovering.Hom.toPresheafTarget f) ≫
        HypercoveringOf.Hom.toSimplicialPresheaf (Hypercovering.Hom.toPresheafTarget g) := by
    change Functor.whiskerRight
        (Hypercovering.Hom.toSimplicialFamily (f ≫ g)) FormalCoproduct.toPresheaf =
      Functor.whiskerRight (Hypercovering.Hom.toSimplicialFamily f)
          FormalCoproduct.toPresheaf ≫
        Functor.whiskerRight (Hypercovering.Hom.toSimplicialFamily g)
          FormalCoproduct.toPresheaf
    simp only [Hypercovering.Hom.toSimplicialFamily, Hypercovering.Hom.toSimplicial,
      Functor.map_comp, Functor.whiskerRight_comp]
  dsimp only [cohomologyMap, HypercoveringOf.Cech.cohomologyMap,
    HypercoveringOf.Cech.complexMap]
  rw [h, NatTrans.rightOp_comp, Functor.whiskerRight_comp, Functor.map_comp,
    HomologicalComplex.homologyMap_comp]

/-- Product sections of fixed-target families, functorially in an additive presheaf. -/
abbrev presheafSectionsInCoefficients :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤
      ((SemiRepresentableFamily.OverFamily.{v, u, w} X)ᵒᵖ ⥤
        AddCommGrpCat.{max u v w}) :=
  Limits.FormalCoproduct.evalOp C AddCommGrpCat.{max u v w} ⋙
    (Functor.whiskeringLeft
      (SemiRepresentableFamily.OverFamily.{v, u, w} X)ᵒᵖ
      (Limits.FormalCoproduct.{w} C)ᵒᵖ AddCommGrpCat.{max u v w}).obj
        SemiRepresentableFamily.OverFamily.forget.op

/-- Product sections of fixed-target families with a fixed additive presheaf. -/
abbrev presheafSectionsFunctor
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    (SemiRepresentableFamily.OverFamily.{v, u, w} X)ᵒᵖ ⥤
      AddCommGrpCat.{max u v w} :=
  presheafSectionsInCoefficients.obj F

/-- Product sections of fixed-target families with coefficients in a sheaf. -/
abbrev familySectionsFunctor
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    (SemiRepresentableFamily.OverFamily.{v, u, w} X)ᵒᵖ ⥤
      AddCommGrpCat.{max u v w} :=
  presheafSectionsFunctor (I.1 ⋙ AddCommGrpCat.uliftFunctor.{u, max w v})

/-- The product-sections complex is the generic presheaf-target construction specialized along
the represented target. -/
abbrev presheafComplexInCoefficients (K : Hypercovering.{w} J X) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  HypercoveringOf.Cech.presheafComplexInCoefficients K.toPresheafTarget

/-- The product-sections complex with a fixed additive presheaf. -/
abbrev presheafComplex (K : Hypercovering.{w} J X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  HypercoveringOf.Cech.presheafComplex K.toPresheafTarget F

/-- Product-sections Cech cohomology is the generic presheaf-target construction specialized
along the represented target. -/
abbrev presheafCohomologyInCoefficients
    (K : Hypercovering.{w} J X) (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤ AddCommGrpCat.{max u v w} :=
  HypercoveringOf.Cech.presheafCohomologyInCoefficients K.toPresheafTarget p

/-- Product-sections Cech cohomology with a fixed additive presheaf. -/
abbrev presheafCohomology (K : Hypercovering.{w} J X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max u v w} :=
  HypercoveringOf.Cech.presheafCohomology K.toPresheafTarget F p

/-- A fixed-target morphism induces the generic product-sections complex map. -/
noncomputable def presheafComplexMap {K L : Hypercovering.{w} J X} (f : K ⟶ L)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    presheafComplex L F ⟶ presheafComplex K F :=
  HypercoveringOf.Cech.presheafComplexMap
    (Hypercovering.Hom.toPresheafTarget f) F

/-- A fixed-target morphism induces the generic map on product-sections Cech cohomology. -/
noncomputable def presheafCohomologyMap
    {K L : Hypercovering.{w} J X} (f : K ⟶ L)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    presheafCohomology L F p ⟶ presheafCohomology K F p :=
  HypercoveringOf.Cech.presheafCohomologyMap
    (Hypercovering.Hom.toPresheafTarget f) F p

omit [HasWeakSheafify J AddCommGrpCat.{max w v}] in
set_option backward.isDefEq.respectTransparency false in
/-- Product-sections Cech cohomology sends identity maps to identities. -/
theorem presheafCohomologyMap_id (K : Hypercovering.{w} J X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    presheafCohomologyMap (𝟙 K) F p = 𝟙 _ := by
  change HomologicalComplex.homologyMap
    ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (Hypercovering.Hom.toSimplicialFamily (𝟙 K)).rightOp
        (SemiRepresentableFamily.Cech.sections F))) p = 𝟙 _
  have h : Hypercovering.Hom.toSimplicialFamily (𝟙 K) = 𝟙 K.simplicialFamily :=
    Functor.whiskerRight_id' SemiRepresentableFamily.OverFamily.forget
  rw [h, NatTrans.rightOp_id, Functor.whiskerRight_id']
  exact (congrArg (fun t ↦ HomologicalComplex.homologyMap t p)
    ((alternatingCofaceMapComplex _).map_id _)).trans
      (HomologicalComplex.homologyMap_id _ p)

omit [HasWeakSheafify J AddCommGrpCat.{max w v}] in
set_option backward.isDefEq.respectTransparency false in
/-- Product-sections Cech cohomology maps respect composition contravariantly. -/
theorem presheafCohomologyMap_comp
    {K L M : Hypercovering.{w} J X} (f : K ⟶ L) (g : L ⟶ M)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    presheafCohomologyMap (f ≫ g) F p =
      presheafCohomologyMap g F p ≫ presheafCohomologyMap f F p := by
  let A := alternatingCofaceMapComplex AddCommGrpCat.{max u v w}
  let S := SemiRepresentableFamily.Cech.sections F
  change HomologicalComplex.homologyMap
      (A.map (Functor.whiskerRight
        (Hypercovering.Hom.toSimplicialFamily (f ≫ g)).rightOp S)) p =
    HomologicalComplex.homologyMap
        (A.map (Functor.whiskerRight
          (Hypercovering.Hom.toSimplicialFamily g).rightOp S)) p ≫
      HomologicalComplex.homologyMap
        (A.map (Functor.whiskerRight
          (Hypercovering.Hom.toSimplicialFamily f).rightOp S)) p
  simp only [Hypercovering.Hom.toSimplicialFamily, Hypercovering.Hom.toSimplicial,
    Functor.map_comp, Functor.whiskerRight_comp, NatTrans.rightOp_comp,
    HomologicalComplex.homologyMap_comp]

omit [HasWeakSheafify J AddCommGrpCat.{max w v}] in
set_option backward.isDefEq.respectTransparency false in
/-- Product-sections Cech cohomology maps are natural in the coefficient presheaf. -/
theorem presheafCohomologyMap_natural
    {K L : Hypercovering.{w} J X} (f : K ⟶ L)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} (phi : F ⟶ G) (p : ℕ) :
    (presheafCohomologyInCoefficients L p).map phi ≫
        presheafCohomologyMap f G p =
      presheafCohomologyMap f F p ≫
        (presheafCohomologyInCoefficients K p).map phi := by
  let A := alternatingCofaceMapComplex AddCommGrpCat.{max u v w}
  have h : (presheafComplexInCoefficients L).map phi ≫ presheafComplexMap f G =
      presheafComplexMap f F ≫ (presheafComplexInCoefficients K).map phi := by
    change A.map (Functor.whiskerLeft L.simplicialFamily.rightOp
        (SemiRepresentableFamily.Cech.sectionsInCoefficients.map phi)) ≫
          A.map (Functor.whiskerRight
            (Hypercovering.Hom.toSimplicialFamily f).rightOp
            (SemiRepresentableFamily.Cech.sections G)) =
      A.map (Functor.whiskerRight
          (Hypercovering.Hom.toSimplicialFamily f).rightOp
          (SemiRepresentableFamily.Cech.sections F)) ≫
        A.map (Functor.whiskerLeft K.simplicialFamily.rightOp
          (SemiRepresentableFamily.Cech.sectionsInCoefficients.map phi))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun t ↦ A.map t)
      (Functor.whiskerLeft_comp_whiskerRight
        (Hypercovering.Hom.toSimplicialFamily f).rightOp
        (SemiRepresentableFamily.Cech.sectionsInCoefficients.map phi))
  simpa only [presheafCohomologyInCoefficients,
    HypercoveringOf.Cech.presheafCohomologyInCoefficients,
    SemiRepresentableFamily.Cech.cohomologyInCoefficients,
    presheafCohomologyMap, HypercoveringOf.Cech.presheafCohomologyMap,
    SemiRepresentableFamily.Cech.cohomologyMap, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map, presheafComplexMap,
    HypercoveringOf.Cech.presheafComplexMap, Functor.map_comp,
    HomologicalComplex.homologyMap_comp] using congrArg (fun t ↦
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
      (ComplexShape.up ℕ) p).map t) h

/-- The alternating-coface complex of products of coefficient sections. -/
abbrev familySectionsComplex (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  presheafComplex K (I.1 ⋙ AddCommGrpCat.uliftFunctor.{u, max w v})

/-- Equation 25.5.2.1 (Tag 01GX): product sections and free-abelian-sheaf sections give
canonically isomorphic Cech complexes. -/
@[stacks 01GX]
theorem familySectionsComplex_isomorphic_complex
    (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    IsIsomorphic (familySectionsComplex K I) (complex K I) := sorry

/-- Cech cohomology is homology of the associated Cech complex. -/
theorem cohomology_def (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p : ℕ) :
    cohomology K I p = (complex K I).homology p := rfl

/-- Lemma 25.5.1 (01GV): degree-zero Cech cohomology is the section group over the fixed
target. -/
@[stacks 01GV]
theorem cohomology_zero_isomorphic_sections
    (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    IsIsomorphic (cohomology K I 0)
      ((AddCommGrpCat.uliftFunctor.{u, max w v}).obj (I.1.obj (op X))) := sorry

/-- For injective coefficients, degree-zero Cech cohomology is the section group over the
fixed target. -/
@[stacks 01GW "degree zero"]
theorem cohomology_zero_isomorphic_sections_of_injective
    (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I] :
    IsIsomorphic (cohomology K I 0)
      ((AddCommGrpCat.uliftFunctor.{u, max w v}).obj (I.1.obj (op X))) :=
  cohomology_zero_isomorphic_sections K I

/-- For injective coefficients, positive-degree fixed-target Cech cohomology vanishes. -/
@[stacks 01GW "positive degrees"]
theorem cohomology_isZero_of_injective_pos
    (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I]
    {p : ℕ} (hp : 0 < p) :
    IsZero (cohomology K I p) := sorry

end CategoryTheory.Hypercovering.Cech
