/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Presheaf.Cech
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Refinement
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian

/-!
# Čech cohomology under presheaf-target hypercovering refinements

This leaf constructs the Čech complex and cohomology of a presheaf-target hypercovering and the
contravariant action of augmentation-preserving refinements.  Homotopic refinements induce the
same cohomology map, so the action descends to the refinement category.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Cech

open AlgebraicTopology Limits Opposite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- The contravariant sections functor obtained by mapping a presheaf to its free abelian
sheafification and then taking morphisms into `I`. -/
abbrev sectionsFunctor (I : Sheaf J AddCommGrpCat.{max w v}) :
    (Cᵒᵖ ⥤ Type (max w v))ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  J.freeAbelianSheafFunctor.op ⋙ preadditiveYoneda.obj I

/-- The sections construction as a functor of the coefficient sheaf. -/
abbrev sectionsInCoefficients :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      ((Cᵒᵖ ⥤ Type (max w v))ᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :=
  preadditiveYoneda ⋙
    (Functor.whiskeringLeft (Cᵒᵖ ⥤ Type (max w v))ᵒᵖ
      (Sheaf J AddCommGrpCat.{max w v})ᵒᵖ
      AddCommGrpCat.{max u v w}).obj J.freeAbelianSheafFunctor.op

/-- The Čech cochain complex of `K`, functorially in the coefficient sheaf. -/
abbrev complexInCoefficients (K : HypercoveringOf J 𝒢) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  sectionsInCoefficients ⋙
    (Functor.whiskeringLeft SimplexCategory
      (Cᵒᵖ ⥤ Type (max w v))ᵒᵖ
      AddCommGrpCat.{max u v w}).obj
        (hypercoveringPresheaf K.simplicial).rightOp ⋙
    alternatingCofaceMapComplex AddCommGrpCat.{max u v w}

/-- Degree-`i` Čech cohomology of `K`, functorially in the coefficient sheaf. -/
abbrev cohomologyInCoefficients (K : HypercoveringOf J 𝒢) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w} :=
  complexInCoefficients K ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
      (ComplexShape.up ℕ) i

/-- The Čech cochain complex of one presheaf-target hypercovering. -/
abbrev complex (K : HypercoveringOf J 𝒢)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  (complexInCoefficients K).obj I

/-- The degree-`i` Čech cohomology object of one presheaf-target hypercovering. -/
abbrev cohomology (K : HypercoveringOf J 𝒢)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max u v w} :=
  (cohomologyInCoefficients K i).obj I

/-- The map of Čech complexes induced contravariantly by an augmentation-preserving
hypercovering map. -/
noncomputable def complexMap {M K : HypercoveringOf J 𝒢} (f : M ⟶ K)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    complex K I ⟶ complex M I :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).map
    (Functor.whiskerRight (HypercoveringOf.Hom.toSimplicialPresheaf f).rightOp
      (sectionsFunctor I))

/-- The map on Čech cohomology induced by an augmentation-preserving refinement. -/
noncomputable def cohomologyMap {M K : HypercoveringOf J 𝒢} (f : M ⟶ K)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    cohomology K I i ⟶ cohomology M I i :=
  HomologicalComplex.homologyMap (complexMap f I) i

/-- The Čech cohomology map induced by an identity refinement is the identity. -/
theorem cohomologyMap_id (K : HypercoveringOf J 𝒢)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    cohomologyMap (𝟙 K) I i = 𝟙 _ := sorry

/-- Čech cohomology maps respect composition of refinements. -/
theorem cohomologyMap_comp {N M K : HypercoveringOf J 𝒢} (f : N ⟶ M) (g : M ⟶ K)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    cohomologyMap (f ≫ g) I i = cohomologyMap g I i ≫ cohomologyMap f I i := sorry

/-- Homotopic augmentation-preserving maps induce the same map on Čech cohomology. -/
theorem cohomologyMap_eq_of_homotopic {M K : HypercoveringOf J 𝒢} (f g : M ⟶ K)
    (h : SimplicialObject.Homotopic
      (HypercoveringOf.Hom.toSimplicial f)
      (HypercoveringOf.Hom.toSimplicial g))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    cohomologyMap f I i = cohomologyMap g I i := sorry

/-- Čech cohomology maps induced by strict refinements are natural in the coefficient sheaf. -/
theorem cohomologyMap_natural {M K : HypercoveringOf J 𝒢} (f : M ⟶ K)
    {I I' : Sheaf J AddCommGrpCat.{max w v}} (φ : I ⟶ I') (i : ℕ) :
    (cohomologyInCoefficients K i).map φ ≫ cohomologyMap f I' i =
      cohomologyMap f I i ≫ (cohomologyInCoefficients M i).map φ := sorry

/-- A strict refinement induces a natural transformation of Čech cohomology functors in the
coefficient sheaf. -/
noncomputable def cohomologyMapNatTrans {M K : HypercoveringOf J 𝒢}
    (f : M ⟶ K) (i : ℕ) :
    cohomologyInCoefficients K i ⟶ cohomologyInCoefficients M i where
  app I := cohomologyMap f I i
  naturality _ _ φ := cohomologyMap_natural f φ i

/-- The coefficient-natural map induced by an identity strict refinement is the identity. -/
theorem cohomologyMapNatTrans_id (K : HypercoveringOf J 𝒢) (i : ℕ) :
    cohomologyMapNatTrans (𝟙 K) i = 𝟙 _ := sorry

/-- Coefficient-natural maps induced by strict refinements respect contravariant composition. -/
theorem cohomologyMapNatTrans_comp {N M K : HypercoveringOf J 𝒢}
    (f : N ⟶ M) (g : M ⟶ K) (i : ℕ) :
    cohomologyMapNatTrans (f ≫ g) i =
      cohomologyMapNatTrans g i ≫ cohomologyMapNatTrans f i := sorry

/-- The strict refinement diagram, valued in Čech cohomology functors of the coefficient
sheaf, before quotienting refinement maps by homotopy. -/
@[stacks 09VZ "strict coefficient-valued refinement diagram"]
noncomputable def rawRefinementDiagram
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    HypercoveringOf.RawRefinementCategory J 𝒢 ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) where
  obj K := cohomologyInCoefficients K.unop i
  map f := cohomologyMapNatTrans f.unop i
  map_id K := cohomologyMapNatTrans_id K.unop i
  map_comp f g := cohomologyMapNatTrans_comp g.unop f.unop i

namespace RawRefinementDiagram

/-- The strict coefficient-valued diagram sends homotopic hypercovering maps to equal natural
transformations. -/
theorem map_eq_of_homotopic
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ)
    {K L : HypercoveringOf J 𝒢} (f g : K ⟶ L)
    (h : SimplicialObject.Homotopic
      (HypercoveringOf.Hom.toSimplicial f)
      (HypercoveringOf.Hom.toSimplicial g)) :
    (rawRefinementDiagram 𝒢 i).rightOp.map f =
      (rawRefinementDiagram 𝒢 i).rightOp.map g := sorry

end RawRefinementDiagram

/-- The homotopy-invariant refinement diagram valued in Čech cohomology functors of the
coefficient sheaf. -/
@[stacks 09VZ "presheaf-target coefficient-valued refinement diagram"]
noncomputable def refinementDiagram
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    HypercoveringOf.RefinementCategory J 𝒢 ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) :=
  (CategoryTheory.Quotient.lift
    (HypercoveringOf.homotopyRel (J := J) (𝒢 := 𝒢))
    (rawRefinementDiagram 𝒢 i).rightOp
    (fun _ _ f g h ↦ RawRefinementDiagram.map_eq_of_homotopic 𝒢 i f g h)).leftOp

/-- The homotopy-invariant degree-`i` Čech cohomology diagram with fixed coefficients. -/
noncomputable def refinementFunctor
    (𝒢 : Cᵒᵖ ⥤ Type (max w v))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    HypercoveringOf.RefinementCategory J 𝒢 ⥤ AddCommGrpCat.{max u v w} :=
  refinementDiagram 𝒢 i ⋙ (evaluation _ _).obj I

/-- Evaluating the refinement diagram at the stage represented by `K` recovers the Čech
cohomology of `K`. -/
@[simp]
theorem refinementFunctor_obj (K : HypercoveringOf J 𝒢)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    (refinementFunctor 𝒢 I i).obj (HypercoveringOf.refinementObject K) =
      cohomology K I i := sorry

/-- On a represented refinement, the quotient diagram uses the canonical Čech cohomology map. -/
@[simp]
theorem refinementFunctor_map_refinement {M K : HypercoveringOf J 𝒢} (f : M ⟶ K)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    (refinementFunctor 𝒢 I i).map (HypercoveringOf.refinementMap f) =
      cohomologyMap f I i := sorry

/-- A refinement class induces a natural transformation between the corresponding Cech
cohomology functors of the coefficient sheaf. -/
noncomputable def refinementNatTrans
    (i : ℕ)
    {K L : HypercoveringOf.RefinementCategory J 𝒢} (f : K ⟶ L) :
    cohomologyInCoefficients K.unop.as i ⟶
      cohomologyInCoefficients L.unop.as i :=
  (refinementDiagram 𝒢 i).map f

/-- The coefficient-natural transformation of an identity refinement is the identity. -/
theorem refinementNatTrans_id
    (i : ℕ)
    (K : HypercoveringOf.RefinementCategory J 𝒢) :
    refinementNatTrans i (𝟙 K) = 𝟙 _ := sorry

/-- Coefficient-natural transformations of refinement classes respect composition. -/
theorem refinementNatTrans_comp
    (i : ℕ)
    {K L M : HypercoveringOf.RefinementCategory J 𝒢}
    (f : K ⟶ L) (g : L ⟶ M) :
    refinementNatTrans i (f ≫ g) =
      refinementNatTrans i f ≫ refinementNatTrans i g := sorry

/-- Evaluating the coefficient-valued diagram recovers the fixed-coefficient refinement
functor. -/
theorem refinementDiagram_evaluation
    (𝒢 : Cᵒᵖ ⥤ Type (max w v))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    refinementDiagram 𝒢 i ⋙ (evaluation _ _).obj I =
      refinementFunctor 𝒢 I i := sorry

/-- The product-sections Cech complex of a presheaf-target hypercovering, functorially in an
additive presheaf of coefficients. -/
abbrev presheafComplexInCoefficients (K : HypercoveringOf J 𝒢) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  SemiRepresentableFamily.Cech.complexInCoefficients K.simplicial

/-- The product-sections Cech complex of a presheaf-target hypercovering with fixed additive
presheaf coefficients. -/
abbrev presheafComplex (K : HypercoveringOf J 𝒢)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  (presheafComplexInCoefficients K).obj F

/-- Product-sections Cech cohomology of a presheaf-target hypercovering, functorially in an
additive presheaf of coefficients. -/
abbrev presheafCohomologyInCoefficients
    (K : HypercoveringOf J 𝒢) (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤ AddCommGrpCat.{max u v w} :=
  SemiRepresentableFamily.Cech.cohomologyInCoefficients K.simplicial p

/-- Product-sections Cech cohomology of a presheaf-target hypercovering with fixed additive
presheaf coefficients. -/
abbrev presheafCohomology (K : HypercoveringOf J 𝒢)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max u v w} :=
  (presheafCohomologyInCoefficients K p).obj F

/-- An augmentation-preserving hypercovering morphism induces a contravariant map of
product-sections Cech complexes. -/
noncomputable def presheafComplexMap
    {K L : HypercoveringOf J 𝒢} (f : K ⟶ L)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    presheafComplex L F ⟶ presheafComplex K F :=
  SemiRepresentableFamily.Cech.complexMap
    (HypercoveringOf.Hom.toSimplicial f) F

/-- The contravariant map on product-sections Cech cohomology induced by an
augmentation-preserving hypercovering morphism. -/
noncomputable def presheafCohomologyMap
    {K L : HypercoveringOf J 𝒢} (f : K ⟶ L)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    presheafCohomology L F p ⟶ presheafCohomology K F p :=
  SemiRepresentableFamily.Cech.cohomologyMap
    (HypercoveringOf.Hom.toSimplicial f) F p

/-- The identity hypercovering morphism induces the identity on product-sections Cech
cohomology. -/
theorem presheafCohomologyMap_id (K : HypercoveringOf J 𝒢)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    presheafCohomologyMap (𝟙 K) F p = 𝟙 _ := sorry

/-- Contravariant product-sections Cech cohomology maps respect composition of
augmentation-preserving hypercovering morphisms. -/
theorem presheafCohomologyMap_comp
    {K L M : HypercoveringOf J 𝒢} (f : K ⟶ L) (g : L ⟶ M)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    presheafCohomologyMap (f ≫ g) F p =
      presheafCohomologyMap g F p ≫ presheafCohomologyMap f F p := sorry

/-- Hypercovering-refinement maps on product-sections Cech cohomology are natural in the
additive-presheaf coefficients. -/
theorem presheafCohomologyMap_natural
    {K L : HypercoveringOf J 𝒢} (f : K ⟶ L)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} (φ : F ⟶ G) (p : ℕ) :
    (presheafCohomologyInCoefficients L p).map φ ≫
        presheafCohomologyMap f G p =
      presheafCohomologyMap f F p ≫
        (presheafCohomologyInCoefficients K p).map φ := sorry

end CategoryTheory.HypercoveringOf.Cech
